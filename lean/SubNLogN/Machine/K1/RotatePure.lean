/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.Contracts.Streams
import Mathlib.Tactic.Linarith

/-!
# K1, K4-ctl pure part (`K1/RotatePure.lean`): the controlled rotation as fiberwise rotations

**Scope (honest summary).** Pure list/index lemmas, proved (no `sorry`), for
`K4RotateCtlStmt` (`SubNLogN/Machine/Contracts/Streams.lean:635`):
* `rotB Q s o f`: rotation of a fiber of `Q` blocks of `s` records by `o` blocks (the last `o`
  blocks first), `chunk m i l`: the `i`-th chunk of size `m`.
* `permByInv_rotCtl`: `permByInv (rotCtlInvAddr Q1 n1 Q2 n2 Q s off) v` is the concatenation over
  the fibers `c` (of `s·Q` records each) of `rotB Q s (offAt c) (chunk (s·Q) c v)`, where `offAt c`
  reads the controls of fiber `c` (`offAt`), for reduced offsets (`off _ _ < Q`).
* `offAt_idx`: the controls of the fiber with mixed-radix index `(p, c1, y1, c2, y2)` are
  `(c1, c2)`.
* Range/chunk bookkeeping: `flatMap_range_mul`, `outR_add`, `drop_chunk`.
-/

namespace SubNLogN.Machine.K1.Rot

open TMFw TMFw.Contracts

section Pure

variable {α : Type}

/-- Rotation of a fiber of `Q` blocks of `s` records by `o` blocks: the last `o` blocks first. -/
def rotB (Q s o : ℕ) (f : List α) : List α := f.drop ((Q - o) * s) ++ f.take ((Q - o) * s)

/-- The `i`-th chunk of size `m`. -/
def chunk (m i : ℕ) (l : List α) : List α := (l.drop (i * m)).take m

theorem length_rotB (Q s o : ℕ) (f : List α) : (rotB Q s o f).length = f.length := by
  simp only [rotB, List.length_append, List.length_drop, List.length_take]
  omega

theorem length_chunk {m i : ℕ} {l : List α} (h : (i + 1) * m ≤ l.length) :
    (chunk m i l).length = m := by
  simp only [chunk, List.length_take, List.length_drop]
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- The source after chunk `i` is the chunk followed by the source after chunk `i + 1`. -/
theorem drop_chunk (m i : ℕ) (l : List α) :
    l.drop (i * m) = chunk m i l ++ l.drop ((i + 1) * m) := by
  rw [chunk, Nat.add_mul, Nat.one_mul, ← List.drop_drop, List.take_append_drop]

theorem flatMap_range_add {β : Type} (G : ℕ → List β) (a b : ℕ) :
    (List.range (a + b)).flatMap G =
      (List.range a).flatMap G ++ (List.range b).flatMap fun j => G (a + j) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem flatMap_range_mul {β : Type} (G : ℕ → List β) :
    ∀ a b, (List.range (a * b)).flatMap G =
      (List.range a).flatMap fun i => (List.range b).flatMap fun j => G (i * b + j)
  | 0, b => by simp
  | a + 1, b => by
    rw [Nat.succ_mul, flatMap_range_add, flatMap_range_mul G a b, List.range_succ,
      List.flatMap_append]
    simp

/-- Outputs of the `m` consecutive fibers starting at fiber `c0`. -/
def outR {β : Type} (G : ℕ → List β) (c0 m : ℕ) : List β :=
  (List.range m).flatMap fun i => G (c0 + i)

theorem outR_zero {β : Type} (G : ℕ → List β) (c0 : ℕ) : outR G c0 0 = [] := by
  simp [outR]

theorem outR_add {β : Type} (G : ℕ → List β) (c0 a b : ℕ) :
    outR G c0 (a + b) = outR G c0 a ++ outR G (c0 + a) b := by
  simp only [outR, flatMap_range_add, Nat.add_assoc]

theorem outR_one {β : Type} (G : ℕ → List β) (c0 : ℕ) : outR G c0 1 = G c0 := by
  simp [outR]

/-- Rotation within one fiber, pointwise: output record `r` is input record
`((r / s + Q - o) % Q)·s + r % s`. -/
theorem map_rot_eq_rotB (Q s o : ℕ) (hoQ : o < Q) (f : List α) (hf : f.length = Q * s)
    (d : α) :
    (List.range (Q * s)).map (fun r => f.getD (((r / s + Q - o) % Q) * s + r % s) d) =
      rotB Q s o f := by
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs
    have : f = [] := List.eq_nil_of_length_eq_zero (by simpa using hf)
    subst this
    simp [rotB]
  apply List.ext_getElem
  · simp [length_rotB, hf]
  intro r h1 h2
  simp only [List.length_map, List.length_range] at h1
  rw [List.getElem_map, List.getElem_range]
  have hrs : r / s < Q := by
    rw [Nat.div_lt_iff_lt_mul hs]
    linarith
  have hmod : r % s < s := Nat.mod_lt _ hs
  have hdm : r / s * s + r % s = r := by rw [Nat.mul_comm]; exact Nat.div_add_mod r s
  have hA : (Q - o) * s ≤ f.length := by
    rw [hf]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  simp only [rotB]
  by_cases hr : r < o * s
  · have hro : r / s < o := by
      rw [Nat.div_lt_iff_lt_mul hs]
      exact hr
    have e1 : (r / s + Q - o) % Q = r / s + (Q - o) := by
      have h1 : r / s + Q - o = r / s + (Q - o) := Nat.add_sub_assoc hoQ.le (r / s)
      have h2 : r / s + (Q - o) < Q := by
        have := Nat.add_lt_add_right hro (Q - o)
        rwa [Nat.add_sub_cancel' hoQ.le] at this
      rw [h1]
      exact Nat.mod_eq_of_lt h2
    have hlen : r < (f.drop ((Q - o) * s)).length := by
      simp only [List.length_drop, hf]
      have : (Q - o) * s + o * s = Q * s := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hoQ.le]
      omega
    rw [List.getElem_append_left hlen, List.getElem_drop, e1]
    have hidx : (r / s + (Q - o)) * s + r % s = (Q - o) * s + r := by
      rw [Nat.add_mul]
      omega
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    · rfl
  · have hro : o ≤ r / s := by
      rw [Nat.le_div_iff_mul_le hs]
      omega
    have e1 : (r / s + Q - o) % Q = r / s - o := by
      have : r / s + Q - o = (r / s - o) + Q := Nat.sub_add_comm hro
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hrs)]
    have hlen : (f.drop ((Q - o) * s)).length ≤ r := by
      simp only [List.length_drop, hf]
      have : (Q - o) * s + o * s = Q * s := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hoQ.le]
      omega
    rw [List.getElem_append_right hlen, List.getElem_take, e1]
    have hlen' : (f.drop ((Q - o) * s)).length = o * s := by
      simp only [List.length_drop, hf]
      have : (Q - o) * s + o * s = Q * s := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hoQ.le]
      omega
    have hidx : (r / s - o) * s + r % s = r - (f.drop ((Q - o) * s)).length := by
      rw [hlen', Nat.sub_mul]
      have : o * s ≤ r / s * s := Nat.mul_le_mul_right _ hro
      omega
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    · rfl

/-- Pointwise read of a chunk. -/
theorem getD_chunk (m c r : ℕ) (l : List α) (d : α) (hr : r < m) :
    (chunk m c l).getD r d = l.getD (c * m + r) d := by
  simp only [chunk, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hr,
    if_true]

theorem div_of_lt {a b n : ℕ} (h : b < n) : (a * n + b) / n = a :=
  Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)

theorem mod_of_lt {a b n : ℕ} (h : b < n) : (a * n + b) % n = b := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt h]

/-- **Blockwise form of `permByInv`.** If `g` maps each block of `F` consecutive addresses into
itself, `permByInv g v` is the concatenation of the blockwise permuted chunks. -/
theorem permByInv_block [Inhabited α] (g : ℕ → ℕ) (v : List α) (N F : ℕ)
    (hv : v.length = N * F) (h : ℕ → ℕ → ℕ)
    (hg : ∀ c r, c < N → r < F → g (c * F + r) = c * F + h c r)
    (hh : ∀ c r, c < N → r < F → h c r < F) :
    permByInv g v = (List.range N).flatMap fun c =>
      (List.range F).map fun r => (chunk F c v).getD (h c r) default := by
  unfold permByInv
  rw [hv, List.map_eq_flatMap, flatMap_range_mul]
  apply List.flatMap_congr
  intro c hc
  rw [List.mem_range] at hc
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro r hr
  rw [List.mem_range] at hr
  rw [hg c r hc hr, getD_chunk F c (h c r) v default (hh c r hc hr)]

/-- The controls of fiber `c` (of `s·Q` records), as `rotCtlInvAddr` reads them. -/
def offAt (Q1 n1 Q2 n2 : ℕ) (off : ℕ → ℕ → ℕ) (c : ℕ) : ℕ :=
  off (c / (n2 * Q2 * n1) % Q1) (c / n2 % Q2)

/-- **The controlled rotation, fiberwise** (reduced offsets). -/
theorem permByInv_rotCtl [Inhabited α] (Q1 n1 Q2 n2 Q s : ℕ) (off : ℕ → ℕ → ℕ)
    (hoff : ∀ c1 c2, off c1 c2 < Q) (v : List α) (N : ℕ) (hv : v.length = N * (s * Q)) :
    permByInv (rotCtlInvAddr Q1 n1 Q2 n2 Q s off) v =
      (List.range N).flatMap fun c => rotB Q s (offAt Q1 n1 Q2 n2 off c) (chunk (s * Q) c v) := by
  rcases Nat.eq_zero_or_pos (s * Q) with h0 | hpos
  · have hv0 : v = [] := List.eq_nil_of_length_eq_zero (by rw [hv, h0, Nat.mul_zero])
    subst hv0
    simp [permByInv, chunk, rotB]
  have hs : 0 < s := Nat.pos_of_mul_pos_right hpos
  have hQ : 0 < Q := Nat.pos_of_mul_pos_left hpos
  rw [permByInv_block _ v N (s * Q) hv
    (fun c r => ((r / s + Q - offAt Q1 n1 Q2 n2 off c) % Q) * s + r % s)]
  · apply List.flatMap_congr
    intro c hc
    rw [List.mem_range] at hc
    have hlen : (chunk (s * Q) c v).length = Q * s := by
      rw [length_chunk (by rw [hv]; exact Nat.mul_le_mul_right _ hc), Nat.mul_comm]
    have := map_rot_eq_rotB Q s (offAt Q1 n1 Q2 n2 off c) (hoff _ _) (chunk (s * Q) c v) hlen
      default
    rw [Nat.mul_comm Q s] at this
    exact this
  · intro c r hc hr
    have hx : c * (s * Q) + r = s * (c * Q + r / s) + r % s := by
      have := Nat.div_add_mod r s
      nlinarith
    have hrs : r / s < Q := by
      rw [Nat.div_lt_iff_lt_mul hs]
      linarith
    have h1 : (c * (s * Q) + r) / (s * Q) = c := div_of_lt hr
    have h2 : (c * (s * Q) + r) / s = c * Q + r / s := by
      rw [hx, Nat.mul_comm s, div_of_lt (Nat.mod_lt _ hs)]
    have h3 : (c * (s * Q) + r) % s = r % s := by
      rw [hx, Nat.mul_comm s, mod_of_lt (Nat.mod_lt _ hs)]
    have h4 : (c * Q + r / s) % Q = r / s := by
      rw [Nat.mul_comm c Q, Nat.mul_add_mod, Nat.mod_eq_of_lt hrs]
    simp only [rotCtlInvAddr, h1, h2, h3, h4, offAt, Nat.mod_eq_of_lt (hoff _ _)]
    ring
  · intro c r _ hr
    have hmod : (r / s + Q - offAt Q1 n1 Q2 n2 off c) % Q < Q := Nat.mod_lt _ hQ
    have : ((r / s + Q - offAt Q1 n1 Q2 n2 off c) % Q) * s + r % s < Q * s := by
      have h5 : ((r / s + Q - offAt Q1 n1 Q2 n2 off c) % Q + 1) * s ≤ Q * s :=
        Nat.mul_le_mul_right _ hmod
      have h6 := Nat.mod_lt r hs
      rw [Nat.add_mul, Nat.one_mul] at h5
      omega
    rw [Nat.mul_comm s Q]
    exact this

/-- The controls of the fiber with mixed-radix index `(p, c1, y1, c2, y2)` are `(c1, c2)`. -/
theorem offAt_idx (Q1 n1 Q2 n2 : ℕ) (off : ℕ → ℕ → ℕ) {p c1 y1 c2 y2 : ℕ} (hc1 : c1 < Q1)
    (hy1 : y1 < n1) (hc2 : c2 < Q2) (hy2 : y2 < n2) :
    offAt Q1 n1 Q2 n2 off ((((p * Q1 + c1) * n1 + y1) * Q2 + c2) * n2 + y2) = off c1 c2 := by
  have e1 : ((((p * Q1 + c1) * n1 + y1) * Q2 + c2) * n2 + y2) / n2 =
      ((p * Q1 + c1) * n1 + y1) * Q2 + c2 := div_of_lt hy2
  have e2 : (((p * Q1 + c1) * n1 + y1) * Q2 + c2) % Q2 = c2 := mod_of_lt hc2
  have e3 : (((p * Q1 + c1) * n1 + y1) * Q2 + c2) / Q2 = (p * Q1 + c1) * n1 + y1 :=
    div_of_lt hc2
  have e4 : ((p * Q1 + c1) * n1 + y1) / n1 = p * Q1 + c1 := div_of_lt hy1
  have e5 : (p * Q1 + c1) % Q1 = c1 := mod_of_lt hc1
  unfold offAt
  rw [e1, e2, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e1, e3, e4, e5]

end Pure

end SubNLogN.Machine.K1.Rot
