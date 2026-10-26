/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.AppC.C6QLeaves

/-!
# Lemma A.8 join/unjoin: value layer (`Machine/AppC/C6JoinPure.lean`)

The two joining maps of `C6QLeaves.lean` factor into `t` single-digit moves of the K1 kernel
`K1MoveDigitMixStmt` (`Contracts/Streams.lean`). Throughout `NG = q^e·G`, `e = t + ℓ`. (Note: `Machine/AppC` and `C6`/`c6` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Lemma A.8 (`lem:transfer12`).)

* **High join** (`c6HJInv (q^t) (q^ℓ) G B`, `(h, g, d₊, d₋) → (d₊, h, g, d₋)`): move `i < t` moves the
  most significant remaining digit of `d₊` to the left across the block `(h, g)` of size `q^e·G`:
  `hjStep q e G B i = moveLeftMixInv q (q^e·G) (q^(e-1-i)·B)` on the shape
  `[A·q^i] × [q^e·G] × [q] × [q^(e-1-i)·B]`. The composite `hjComp … t` (inverse convention: the last
  move is applied first to an output index) is `c6HJInv` (`c6HJInv_eq_hjComp`).
* **Unjoin** (`c6UJInv (q^t) (q^ℓ) G B`, `(d₊, h₊, d₋, g, h₋) → (d₊, d₋, g, h₊, h₋)`): move `i < t` moves
  the least significant remaining digit of `h₊` to the right across the block `(d₋, g)` of size
  `q^ℓ·G`: `ujStep q ℓ G B i = moveRightMixInv q (q^ℓ·G) (q^(ℓ+i)·B)` on the shape
  `[A·q^t·q^(t-1-i)] × [q] × [q^ℓ·G] × [q^(ℓ+i)·B]`; the composite `ujComp … t` is `c6UJInv`.
* List level: `permByInv (hjComp … (j+1)) v = permByInv (hjStep … j) (permByInv (hjComp … j) v)`
  (and for `uj`), so the arrays after `j` moves are `permByInv (hjComp … j) v`.
-/

namespace SubNLogN.Machine

open TMFw TMFw.Contracts

namespace AppC.C6JoinAux

open AppC.C6Aux

/-! ### Single moves on coordinates -/

theorem moveLeft_coord {q N1 N2 x0 d x1 x2 : ℕ} (hd : d < q) (hx1 : x1 < N1) (hx2 : x2 < N2) :
    moveLeftMixInv q N1 N2 (((x0 * q + d) * N1 + x1) * N2 + x2) =
      ((x0 * N1 + x1) * q + d) * N2 + x2 := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := (x0 * q + d) * N1 + x1) hx2
  obtain ⟨e3, e4⟩ := divmod_aux (q := x0 * q + d) hx1
  obtain ⟨e5, e6⟩ := divmod_aux (q := x0) hd
  simp only [moveLeftMixInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6]

theorem moveRight_coord {q N1 N2 x0 d x1 x2 : ℕ} (hd : d < q) (hx1 : x1 < N1) (hx2 : x2 < N2) :
    moveRightMixInv q N1 N2 (((x0 * N1 + x1) * q + d) * N2 + x2) =
      ((x0 * q + d) * N1 + x1) * N2 + x2 := by
  obtain ⟨e1, e2⟩ := divmod_aux (q := (x0 * N1 + x1) * q + d) hx2
  obtain ⟨e3, e4⟩ := divmod_aux (q := x0 * N1 + x1) hd
  obtain ⟨e5, e6⟩ := divmod_aux (q := x0) hx1
  simp only [moveRightMixInv, ← Nat.div_div_eq_div_mul, e1, e2, e3, e4, e5, e6]

/-- The left move maps the index range of `[N0] × [q] × [N1] × [N2]` into itself. -/
theorem moveLeft_lt {q N0 N1 N2 y : ℕ} (hy : y < N0 * q * N1 * N2) :
    moveLeftMixInv q N1 N2 y < N0 * q * N1 * N2 := by
  obtain ⟨x0, d, x1, x2, h0, hd, h1, h2, rfl⟩ := decomp3 hy
  rw [moveLeft_coord hd h1 h2]
  have : ((x0 * N1 + x1) * q + d) * N2 + x2 < N0 * N1 * q * N2 :=
    add_mul_lt (add_mul_lt (add_mul_lt h0 h1) hd) h2
  calc _ < N0 * N1 * q * N2 := this
    _ = N0 * q * N1 * N2 := by ring

/-- The right move maps the index range of `[N0] × [N1] × [q] × [N2]` into itself. -/
theorem moveRight_lt {q N0 N1 N2 y : ℕ} (hy : y < N0 * N1 * q * N2) :
    moveRightMixInv q N1 N2 y < N0 * N1 * q * N2 := by
  obtain ⟨x0, x1, d, x2, h0, h1, hd, h2, rfl⟩ := decomp3 hy
  rw [moveRight_coord hd h1 h2]
  have : ((x0 * q + d) * N1 + x1) * N2 + x2 < N0 * q * N1 * N2 :=
    add_mul_lt (add_mul_lt (add_mul_lt h0 hd) h1) h2
  calc _ < N0 * q * N1 * N2 := this
    _ = N0 * N1 * q * N2 := by ring

/-! ### The high join -/

/-- Move `i` of the high join. -/
def hjStep (q e G B i : ℕ) : ℕ → ℕ := moveLeftMixInv q (q ^ e * G) (q ^ (e - 1 - i) * B)

/-- The first `j` moves of the high join, as an inverse address map. -/
def hjComp (q e G B : ℕ) : ℕ → ℕ → ℕ
  | 0 => fun y => y
  | j + 1 => fun y => hjComp q e G B j (hjStep q e G B j y)

theorem hjComp_coord {q e G B : ℕ} (hq : 0 < q) : ∀ j, j ≤ e → ∀ a u x r, u < q ^ j →
    x < q ^ e * G → r < q ^ (e - j) * B →
    hjComp q e G B j (((a * q ^ j + u) * (q ^ e * G) + x) * (q ^ (e - j) * B) + r) =
      (a * (q ^ e * G) + x) * (q ^ e * B) + u * (q ^ (e - j) * B) + r := by
  intro j
  induction j with
  | zero =>
    intro _ a u x r hu _ _
    have hu0 : u = 0 := by simpa using hu
    subst hu0
    simp only [hjComp, pow_zero, mul_one, add_zero, Nat.sub_zero, zero_mul]
  | succ j ih =>
    intro hj a u x r hu hx hr
    have hRj : q ^ (e - j) * B = q * (q ^ (e - (j + 1)) * B) := by
      rw [show e - j = e - (j + 1) + 1 by omega, pow_succ]; ring
    have hd : u % q < q := Nat.mod_lt _ hq
    have hu' : u / q < q ^ j := by
      rw [Nat.div_lt_iff_lt_mul hq]
      calc u < q ^ (j + 1) := hu
        _ = q ^ j * q := pow_succ q j
    have hau : a * q ^ (j + 1) + u = (a * q ^ j + u / q) * q + u % q := by
      calc a * q ^ (j + 1) + u = a * q ^ j * q + (q * (u / q) + u % q) := by
            rw [Nat.div_add_mod, pow_succ]; ring
        _ = (a * q ^ j + u / q) * q + u % q := by ring
    have hy : ((a * q ^ (j + 1) + u) * (q ^ e * G) + x) * (q ^ (e - (j + 1)) * B) + r =
        (((a * q ^ j + u / q) * q + u % q) * (q ^ e * G) + x) * (q ^ (e - 1 - j) * B) + r := by
      rw [hau, show e - 1 - j = e - (j + 1) by omega]
    have hr' : u % q * (q ^ (e - (j + 1)) * B) + r < q ^ (e - j) * B := by
      rw [hRj]
      exact add_mul_lt hd hr
    show hjComp q e G B j (hjStep q e G B j _) = _
    rw [hy, hjStep, moveLeft_coord hd hx (by rw [show e - 1 - j = e - (j + 1) by omega]; exact hr)]
    have hz : ((((a * q ^ j + u / q) * (q ^ e * G) + x) * q + u % q) * (q ^ (e - 1 - j) * B) + r) =
        ((a * q ^ j + u / q) * (q ^ e * G) + x) * (q ^ (e - j) * B) +
          (u % q * (q ^ (e - (j + 1)) * B) + r) := by
      rw [hRj, show e - 1 - j = e - (j + 1) by omega]
      ring
    rw [hz, ih (by omega) a (u / q) x _ hu' hx hr']
    have := Nat.div_add_mod u q
    rw [hRj]
    nlinarith [this]

/-- The high join is the composite of its `t` moves (on the index range). -/
theorem c6HJInv_eq_hjComp {q e t A G B y : ℕ} (hq : 0 < q) (ht : t ≤ e)
    (hy : y < A * q ^ e * G * q ^ e * B) :
    c6HJInv (q ^ t) (q ^ (e - t)) G B y = hjComp q e G B t y := by
  have hqe : q ^ e = q ^ t * q ^ (e - t) := by rw [← pow_add, Nat.add_sub_cancel' ht]
  have hy7 : y < A * q ^ t * q ^ t * q ^ (e - t) * G * q ^ (e - t) * B := by
    calc y < A * q ^ e * G * q ^ e * B := hy
      _ = A * q ^ t * q ^ t * q ^ (e - t) * G * q ^ (e - t) * B := by rw [hqe]; ring
  obtain ⟨a, dp, hp, hm, g, dm, z, _, hdp, hhp, hhm, hg, hdm, hz, rfl⟩ := decomp7 hy7
  rw [c6HJInv_coord hdp hhp hhm hg hdm hz]
  have hx : (hp * q ^ (e - t) + hm) * G + g < q ^ e * G := by
    rw [hqe]
    exact add_mul_lt (add_mul_lt hhp hhm) hg
  have hr : dm * B + z < q ^ (e - t) * B := add_mul_lt hdm hz
  have key := hjComp_coord hq t ht a dp ((hp * q ^ (e - t) + hm) * G + g) (dm * B + z) hdp hx hr
  have e1 : ((((((a * q ^ t + dp) * q ^ t + hp) * q ^ (e - t) + hm) * G + g) * q ^ (e - t) + dm) *
      B + z) = ((a * q ^ t + dp) * (q ^ e * G) + ((hp * q ^ (e - t) + hm) * G + g)) *
        (q ^ (e - t) * B) + (dm * B + z) := by
    rw [hqe]; ring
  rw [e1, key, hqe]
  ring

/-- The arrays of the high join: one more move is one more `permByInv`. -/
theorem permByInv_hjComp_succ {α : Type} [Inhabited α] {q e G B A j : ℕ}
    (hj : j + 1 ≤ e) (v : List α) (hv : v.length = A * q ^ e * G * q ^ e * B) :
    permByInv (hjComp q e G B (j + 1)) v =
      permByInv (hjStep q e G B j) (permByInv (hjComp q e G B j) v) := by
  have hlen : v.length = (A * q ^ j) * q * (q ^ e * G) * (q ^ (e - 1 - j) * B) := by
    rw [hv]
    have : q ^ e = q ^ j * q * q ^ (e - 1 - j) := by
      rw [← pow_succ, ← pow_add, show j + 1 + (e - 1 - j) = e by omega]
    rw [this]
    ring
  rw [permByInv_comp _ _ v (fun y hy => by rw [hlen] at hy ⊢; exact moveLeft_lt hy)]
  rfl


/-! ### The unjoin -/

/-- Move `i` of the unjoin. -/
def ujStep (q l G B i : ℕ) : ℕ → ℕ := moveRightMixInv q (q ^ l * G) (q ^ (l + i) * B)

/-- The first `j` moves of the unjoin, as an inverse address map. -/
def ujComp (q l G B : ℕ) : ℕ → ℕ → ℕ
  | 0 => fun y => y
  | j + 1 => fun y => ujComp q l G B j (ujStep q l G B j y)

theorem ujComp_coord {q l t G B : ℕ} (hq : 0 < q) : ∀ j, j ≤ t → ∀ P hh x w r, hh < q ^ (t - j) →
    x < q ^ l * G → w < q ^ j → r < q ^ l * B →
    ujComp q l G B j (((P * q ^ (t - j) + hh) * (q ^ l * G) + x) * (q ^ (l + j) * B) +
        (w * (q ^ l * B) + r)) =
      ((P * q ^ t + hh * q ^ j + w) * (q ^ l * G) + x) * (q ^ l * B) + r := by
  intro j
  induction j with
  | zero =>
    intro _ P hh x w r _ _ hw _
    have hw0 : w = 0 := by simpa using hw
    subst hw0
    simp only [ujComp, pow_zero, mul_one, add_zero, Nat.sub_zero, zero_mul, zero_add]
  | succ j ih =>
    intro hj P hh x w r hh' hx hw hr
    have hqj : 0 < q ^ j := pow_pos hq j
    have hd : w / q ^ j < q := by
      rw [Nat.div_lt_iff_lt_mul hqj]
      calc w < q ^ (j + 1) := hw
        _ = q * q ^ j := pow_succ' q j
    have hw0 : w % q ^ j < q ^ j := Nat.mod_lt _ hqj
    have hx2 : w % q ^ j * (q ^ l * B) + r < q ^ (l + j) * B := by
      rw [show q ^ (l + j) * B = q ^ j * (q ^ l * B) by rw [pow_add]; ring]
      exact add_mul_lt hw0 hr
    have hsplit : w = w / q ^ j * q ^ j + w % q ^ j := (Nat.div_add_mod' w (q ^ j)).symm
    have hy : ((P * q ^ (t - (j + 1)) + hh) * (q ^ l * G) + x) * (q ^ (l + (j + 1)) * B) +
        (w * (q ^ l * B) + r) =
        (((P * q ^ (t - (j + 1)) + hh) * (q ^ l * G) + x) * q + w / q ^ j) * (q ^ (l + j) * B) +
          (w % q ^ j * (q ^ l * B) + r) := by
      conv_lhs => rw [hsplit]
      rw [show l + (j + 1) = l + j + 1 by omega, pow_succ, pow_add]
      ring
    show ujComp q l G B j (ujStep q l G B j _) = _
    rw [hy, ujStep, moveRight_coord hd hx hx2]
    have hh2 : (P * q ^ (t - (j + 1)) + hh) * q + w / q ^ j =
        P * q ^ (t - j) + (hh * q + w / q ^ j) := by
      rw [show t - j = t - (j + 1) + 1 by omega, pow_succ]; ring
    have hhb : hh * q + w / q ^ j < q ^ (t - j) := by
      rw [show t - j = t - (j + 1) + 1 by omega, pow_succ]
      exact add_mul_lt hh' hd
    rw [hh2, ih (by omega) P (hh * q + w / q ^ j) x (w % q ^ j) r hhb hx hw0 hr]
    have hD : P * q ^ t + (hh * q + w / q ^ j) * q ^ j + w % q ^ j =
        P * q ^ t + hh * q ^ (j + 1) + w :=
      calc P * q ^ t + (hh * q + w / q ^ j) * q ^ j + w % q ^ j
          = P * q ^ t + hh * (q * q ^ j) + (w / q ^ j * q ^ j + w % q ^ j) := by ring
        _ = P * q ^ t + hh * q ^ (j + 1) + w := by rw [← hsplit, pow_succ']
    rw [hD]

/-- The unjoin is the composite of its `t` moves (on the index range). -/
theorem c6UJInv_eq_ujComp {q e t A G B y : ℕ} (hq : 0 < q)
    (hy : y < A * q ^ t * q ^ t * q ^ (e - t) * G * q ^ (e - t) * B) :
    c6UJInv (q ^ t) (q ^ (e - t)) G B y = ujComp q (e - t) G B t y := by
  have hy7 : y < A * q ^ t * q ^ (e - t) * G * q ^ t * q ^ (e - t) * B := by
    calc y < A * q ^ t * q ^ t * q ^ (e - t) * G * q ^ (e - t) * B := hy
      _ = A * q ^ t * q ^ (e - t) * G * q ^ t * q ^ (e - t) * B := by ring
  obtain ⟨a, dp, dm, g, hp, hm, z, _, hdp, hdm, hg, hhp, hhm, hz, rfl⟩ := decomp7 hy7
  rw [c6UJInv_coord hdp hdm hg hhp hhm hz]
  have hx : dm * G + g < q ^ (e - t) * G := add_mul_lt hdm hg
  have hr : hm * B + z < q ^ (e - t) * B := add_mul_lt hhm hz
  have key := ujComp_coord (l := e - t) (t := t) (G := G) (B := B) hq t le_rfl (a * q ^ t + dp) 0
    (dm * G + g) hp (hm * B + z) (by simp) hx hhp hr
  have e1 : (((((a * q ^ t + dp) * q ^ (e - t) + dm) * G + g) * q ^ t + hp) * q ^ (e - t) + hm) *
      B + z = (((a * q ^ t + dp) * q ^ (t - t) + 0) * (q ^ (e - t) * G) + (dm * G + g)) *
        (q ^ (e - t + t) * B) + (hp * (q ^ (e - t) * B) + (hm * B + z)) := by
    rw [Nat.sub_self, pow_zero, pow_add]; ring
  rw [e1, key]
  ring

/-- The arrays of the unjoin: one more move is one more `permByInv`. -/
theorem permByInv_ujComp_succ {α : Type} [Inhabited α] {q l t G B A j : ℕ} (hj : j + 1 ≤ t)
    (v : List α) (hv : v.length = A * q ^ t * q ^ t * q ^ l * G * q ^ l * B) :
    permByInv (ujComp q l G B (j + 1)) v =
      permByInv (ujStep q l G B j) (permByInv (ujComp q l G B j) v) := by
  have hlen : v.length = (A * q ^ t * q ^ (t - 1 - j)) * (q ^ l * G) * q * (q ^ (l + j) * B) := by
    rw [hv]
    have : q ^ t = q ^ (t - 1 - j) * q * q ^ j := by
      rw [← pow_succ, ← pow_add, show t - 1 - j + 1 + j = t by omega]
    rw [pow_add]
    nth_rewrite 2 [this]
    ring
  rw [permByInv_comp _ _ v (fun y hy => by rw [hlen] at hy ⊢; exact moveRight_lt hy)]
  rfl

end AppC.C6JoinAux

end SubNLogN.Machine
