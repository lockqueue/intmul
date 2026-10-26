/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C5Leaves

/-!
# Proposition A.7, concrete network data (`AppC/C5Net.lean`)

A concrete network instance (`NetData`): stream operations are *macros* (lists of the static
`StreamOp`s of leaf L2, applied left to right; e.g. `D ← D − H` = `hdShift i i true` for all `i`),
gates are lists of elementary XORs `(target, source)` (leaf L3), a static schedule, the outer shears
`pre`/`post`, the merge order `ρ`. `NetData.toNet` gives the abstract `Net` of the skeleton.
Pure facts proved here: every `streamMap` (hence every macro) maps indices into the same row
(`streamMap_lt`, `macroMap_lt`), gates preserve shapes (`gateApply_shape`), and `permByInv`
composes (`permByInv_comp`). The remaining network facts form the leaf `C5NetStmt` (L6-L8). (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)
-/

namespace SubNLogN.Machine.C5

open TMFw TMFw.Contracts

/-- **Static data of a concrete Proposition A.7 network instance.** -/
structure NetData (W m : ℕ) where
  /-- number of stream macros -/
  nOps : ℕ
  /-- the stream macros (applied left to right) -/
  ops : Fin nOps → List (StreamOp m)
  /-- number of gates -/
  nG : ℕ
  /-- the gates, as elementary XORs `(target, source)` (applied left to right) -/
  gates : Fin nG → List (Fin W × Fin W)
  /-- the node schedule -/
  sched : List (SchedOp W m (Fin nOps) (Fin nG))
  /-- `D ← D − H` -/
  pre : Fin nOps
  /-- `D ← H − D` -/
  post : Fin nOps
  /-- merge order -/
  ρ : Equiv.Perm (Fin W)

/-- Inverse address map of a macro (ops applied left to right): `f₁ ∘ f₂ ∘ ⋯ ∘ fₗ`. -/
def macroMap (q m : ℕ) (ops : List (StreamOp m)) (k N1 G B : ℕ) : ℕ → ℕ :=
  ops.foldr (fun o g => streamMap q m o k N1 G B ∘ g) id

/-- One elementary XOR on the role arrays: `us t ← xorArr (us t) (us s)`. -/
def xorStep {W : ℕ} (us : Fin W → List (List Bool)) (p : Fin W × Fin W) :
    Fin W → List (List Bool) :=
  Function.update us p.1 (xorArr (us p.1) (us p.2))

/-- A gate: its elementary XORs left to right. -/
def gateApply {W : ℕ} (l : List (Fin W × Fin W)) (us : Fin W → List (List Bool)) :
    Fin W → List (List Bool) :=
  l.foldl xorStep us

/-- The abstract network of a concrete instance at the radix base `q`. -/
def NetData.toNet {W m : ℕ} (q : ℕ) (D : NetData W m) : Net W m where
  Op := Fin D.nOps
  Gt := Fin D.nG
  sched := D.sched
  streamMap o := macroMap q m (D.ops o)
  gateF g := gateApply (D.gates g)
  pre := D.pre
  post := D.post
  ρ := D.ρ

/-! ## Index arithmetic -/

/-- Replacing one digit (radix `Qd`, place value `P`) keeps an index inside its block of `P·Qd`,
hence below any multiple `n` of `P·Qd` that bounds it. -/
theorem replace_digit_lt {y P Qd n hv : ℕ} (hP : 0 < P) (hdvd : P * Qd ∣ n) (hy : y < n)
    (hv' : hv < Qd) : y - y / P % Qd * P + hv * P < n := by
  have hQd : 0 < Qd := by omega
  have hM : 0 < P * Qd := Nat.mul_pos hP hQd
  have e1 : y = y / P * P + y % P := (Nat.div_add_mod' y P).symm
  have e2 : y / P = y / P / Qd * Qd + y / P % Qd := (Nat.div_add_mod' (y / P) Qd).symm
  have e3 : y / P / Qd = y / (P * Qd) := Nat.div_div_eq_div_mul y P Qd
  have hr : y % P < P := Nat.mod_lt _ hP
  obtain ⟨t, ht⟩ := hdvd
  have hat : y / (P * Qd) < t := by
    rw [Nat.div_lt_iff_lt_mul hM]
    calc y < n := hy
      _ = t * (P * Qd) := by rw [ht, Nat.mul_comm]
  have hy' : y = y / (P * Qd) * (P * Qd) + y / P % Qd * P + y % P := by
    rw [e3] at e2
    calc y = y / P * P + y % P := e1
      _ = (y / (P * Qd) * Qd + y / P % Qd) * P + y % P := by rw [← e2]
      _ = y / (P * Qd) * (P * Qd) + y / P % Qd * P + y % P := by ring
  have h1 : y / (P * Qd) * (P * Qd) + P * Qd ≤ n := by
    have hat' : y / (P * Qd) + 1 ≤ t := hat
    have h := Nat.mul_le_mul_right (P * Qd) hat'
    rw [add_one_mul] at h
    rw [ht, Nat.mul_comm (P * Qd) t]
    exact h
  have h2 : hv * P + P ≤ P * Qd := by
    have hv'' : hv + 1 ≤ Qd := hv'
    have h := Nat.mul_le_mul_right P hv''
    rw [add_one_mul, Nat.mul_comm Qd P] at h
    exact h
  omega

theorem pow_m_eq (q m k : ℕ) (hk : 1 ≤ k) : (q ^ m ^ (k - 1)) ^ m = q ^ m ^ k := by
  rw [← pow_mul, ← pow_succ]
  congr 2
  omega

theorem setCoordOf_lt {m Q cv i d : ℕ} (hi : i < m) (hcv : cv < Q ^ m) (hd : d < Q) :
    setCoordOf m Q cv i d < Q ^ m := by
  have hQ : 0 < Q := by omega
  unfold setCoordOf coordOf
  refine replace_digit_lt (pow_pos hQ _) ?_ hcv hd
  rw [← pow_succ]
  exact pow_dvd_pow Q (by omega)

theorem chunkVal_lt {Qe G B : ℕ} (hQe : 0 < Qe) (X : Chunk) (y : ℕ) : chunkVal Qe G B X y < Qe := by
  cases X <;> exact Nat.mod_lt _ hQe

theorem setChunk_lt {Qe G B n y v : ℕ} (X : Chunk) (hB : 0 < B) (hG : 0 < G)
    (hdvd : B * Qe * G * Qe ∣ n) (hy : y < n) (hv : v < Qe) : setChunk Qe G B X y v < n := by
  have hQe : 0 < Qe := by omega
  cases X with
  | H =>
    show y - y / (B * Qe * G) % Qe * (B * Qe * G) + v * (B * Qe * G) < n
    exact replace_digit_lt (Nat.mul_pos (Nat.mul_pos hB hQe) hG) hdvd hy hv
  | D =>
    show y - y / B % Qe * B + v * B < n
    refine replace_digit_lt hB (dvd_trans ⟨G * Qe, by ring⟩ hdvd) hy hv

/-- **Stream operations stay inside their row** (`k ≥ 1`, `q ≥ 1`): for `n` a multiple of the row
size and `y < n`, `streamMap … y < n`. -/
theorem streamMap_lt (q m : ℕ) (op : StreamOp m) (k N1 G B n : ℕ) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hdvd : rowSize q m k N1 G B ∣ n) (y : ℕ) (hy : y < n) : streamMap q m op k N1 G B y < n := by
  rcases Nat.eq_zero_or_pos B with hB0 | hB
  · subst hB0
    simp [rowSize] at hdvd
    omega
  rcases Nat.eq_zero_or_pos G with hG0 | hG
  · subst hG0
    simp [rowSize] at hdvd
    omega
  have hQ : 0 < q ^ m ^ (k - 1) := pow_pos (by omega) _
  have hQe : 0 < q ^ m ^ k := pow_pos (by omega) _
  have hd : B * q ^ m ^ k * G * q ^ m ^ k ∣ n :=
    dvd_trans ⟨N1, by simp only [rowSize]; ring⟩ hdvd
  have hpow := pow_m_eq q m k hk
  cases op with
  | unit X i r =>
    dsimp only [streamMap]
    exact setChunk_lt X hB hG hd hy (hpow ▸ setCoordOf_lt i.isLt (hpow ▸ chunkVal_lt (G := G) (B := B) hQe X y)
      (Nat.mod_lt _ hQ))
  | lowShift X i c =>
    dsimp only [streamMap]
    exact setChunk_lt X hB hG hd hy (hpow ▸ setCoordOf_lt i.isLt (hpow ▸ chunkVal_lt (G := G) (B := B) hQe X y)
      (Nat.mod_lt _ hQ))
  | hdShift i j neg =>
    dsimp only [streamMap]
    refine setChunk_lt .D hB hG hd hy (hpow ▸ setCoordOf_lt j.isLt
      (hpow ▸ chunkVal_lt (G := G) (B := B) hQe .D y) ?_)
    split_ifs <;> exact Nat.mod_lt _ hQ

theorem macroMap_cons (q m : ℕ) (o : StreamOp m) (os : List (StreamOp m)) (k N1 G B : ℕ) :
    macroMap q m (o :: os) k N1 G B = streamMap q m o k N1 G B ∘ macroMap q m os k N1 G B := rfl

theorem macroMap_lt (q m : ℕ) (ops : List (StreamOp m)) (k N1 G B n : ℕ) (hq : 1 ≤ q)
    (hk : 1 ≤ k) (hdvd : rowSize q m k N1 G B ∣ n) : ∀ y < n, macroMap q m ops k N1 G B y < n := by
  induction ops with
  | nil => intro y hy; exact hy
  | cons o os ih =>
    intro y hy
    rw [macroMap_cons]
    exact streamMap_lt q m o k N1 G B n hq hk hdvd _ (ih y hy)

theorem foldr_comp_init {α : Type} (f : α → (ℕ → ℕ)) (h : ℕ → ℕ) (l : List α) :
    l.foldr (fun o g => f o ∘ g) h = l.foldr (fun o g => f o ∘ g) id ∘ h := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.foldr_cons, ih, Function.comp_assoc]

theorem macroMap_append_one (q m : ℕ) (os : List (StreamOp m)) (o : StreamOp m) (k N1 G B : ℕ) :
    macroMap q m (os ++ [o]) k N1 G B = macroMap q m os k N1 G B ∘ streamMap q m o k N1 G B := by
  unfold macroMap
  rw [List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_comp_init]
  rfl

/-- `permByInv` composes (the inner map stays in range). -/
theorem permByInv_comp (f g : ℕ → ℕ) (v : List (List Bool)) (hf : ∀ y < v.length, f y < v.length) :
    permByInv f (permByInv g v) = permByInv (g ∘ f) v := by
  simp only [permByInv, List.length_map, List.length_range]
  refine List.map_congr_left (fun y hy => ?_)
  rw [List.mem_range] at hy
  rw [List.getD_eq_getElem _ _ (by simpa using hf y hy)]
  simp

/-! ## Gates -/

theorem xorArr_length (a b : List (List Bool)) (h : a.length = b.length) :
    (xorArr a b).length = a.length := by
  simp [xorArr, List.length_zipWith, h]

theorem xorArr_widths : ∀ (a b : List (List Bool)) (w : ℕ), (∀ p ∈ a, p.length = w) →
    (∀ p ∈ b, p.length = w) → ∀ p ∈ xorArr a b, p.length = w
  | [], _, _, _, _ => by simp [xorArr]
  | _ :: _, [], _, _, _ => by simp [xorArr]
  | x :: a, y :: b, w, ha, hb => by
    intro p hp
    simp only [xorArr, List.zipWith_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp [List.length_zipWith, ha x (by simp), hb y (by simp)]
    · exact xorArr_widths a b w (fun p h => ha p (by simp [h])) (fun p h => hb p (by simp [h])) p hp

theorem gateApply_shape {W : ℕ} (l : List (Fin W × Fin W)) (n w : ℕ) :
    ∀ us : Fin W → List (List Bool), (∀ r, (us r).length = n) → (∀ r, ∀ p ∈ us r, p.length = w) →
      (∀ r, (gateApply l us r).length = n) ∧ (∀ r, ∀ p ∈ gateApply l us r, p.length = w) := by
  induction l with
  | nil => intro us h1 h2; exact ⟨h1, h2⟩
  | cons p l ih =>
    intro us h1 h2
    refine ih (xorStep us p) (fun r => ?_) (fun r => ?_)
    · by_cases hr : r = p.1
      · subst hr
        simp only [xorStep, Function.update_self]
        rw [xorArr_length _ _ (by rw [h1, h1]), h1]
      · simp only [xorStep, Function.update_of_ne hr]
        exact h1 r
    · by_cases hr : r = p.1
      · subst hr
        simp only [xorStep, Function.update_self]
        exact xorArr_widths _ _ w (h2 _) (h2 _)
      · simp only [xorStep, Function.update_of_ne hr]
        exact h2 r

/-! ## The network leaf -/

/-- **[LEAF L6-L8, pure math] A concrete network instance for Proposition A.7** (the image of
`bitNodeOps`, `Math/Networks/AppCProc.lean`; Proposition A.7 (`prop:transfer11`)): `W_b = tripleWb 100`
roles, stream macros whose operations are valid at `q`, XOR gates on distinct roles, at most
`s_b = tripleSb 100` pivot calls per node (L8), and node correctness (L6+L7, `NodeCorrect`: `pre`,
cyclic row split, the schedule with calls acting as exact level-`k-1` interchanges, merge in order
`ρ`, `post` = the level-`k` interchange). -/
def C5NetStmt (q : ℕ) : Prop :=
  ∃ D : NetData (tripleWb 100) (tripleM 100),
    NodeCorrect q (D.toNet q) ∧ (D.sched.filter SchedOp.isCall).length ≤ tripleSb 100 ∧
      (∀ o, ∀ op ∈ D.ops o, op.Valid q) ∧ (∀ g, ∀ p ∈ D.gates g, p.1 ≠ p.2)

/-- The skeleton's `NetFacts` for a concrete instance (stream and gate facts are proved here). -/
theorem netFacts_of_data {W m : ℕ} (q : ℕ) (hq : 1 ≤ q) (D : NetData W m) (s : ℕ)
    (hnode : NodeCorrect q (D.toNet q)) (hcalls : (D.sched.filter SchedOp.isCall).length ≤ s) :
    NetFacts q (D.toNet q) s where
  node := hnode
  stream_lt o k N1 G B n hk hdvd := macroMap_lt q m (D.ops o) k N1 G B n hq hk hdvd
  gate_shape g us n w h1 h2 := gateApply_shape (D.gates g) n w us h1 h2
  calls_le := hcalls

end SubNLogN.Machine.C5
