/-
Copyright (c) 2026 The Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SubNLogN.Machine.K1.DigitPairPermMix

/-!
# K1b-mix (`K1/DigitMoveDigitMix.lean`): move a digit across a spectator block, mixed shape

Paper: Fact 3.3(1) (`fact:oai-streams`) and Lemma A.4(2) (`lem:transfer-streams`,
proof: `q` streams; the selected digit is inserted at another
place of the nested merge).

**Scope (honest summary).** Proves `k1MoveDigitMix_holds : K1MoveDigitMixStmt q toRight` for every
`q` and both directions (`Contracts/Streams.lean`, `K1MoveDigitMixStmt`), with no extra hypotheses.
* `q = 0`: the array is empty; the program is `skip`.
* `q ≥ 1`: `mixProg` (`K1/DigitMix.lean`) with `q` streams (key component `A` only):
  - `toRight`: distribute over the input nest `[A, R 0, R 1]` (shape `[N0] × [q] × [N1] × [N2]`),
    merge over the output nest `[R 0, A, R 1]` (shape `[N0] × [N1] × [q] × [N2]`);
  - `toLeft`: the two nests exchanged.
  On each fiber of the moved digit both address orders are the lexicographic order of
  `(x0, x1, x2)` (`lex_L`, `lex_R`), which is the merge consistency condition.
Cost `C·(V + 1)`.
-/

namespace SubNLogN.Machine.K1Digit

open TMFw TMFw.Contracts TMFw.Lib

/-! ## Lexicographic order of the two layouts -/

theorem mono_aux {P P' c c' n : ℕ} (hc : c < n) (hc' : c' < n) (h : P * n + c < P' * n + c') :
    P < P' ∨ (P = P' ∧ c < c') := by
  rcases Nat.lt_trichotomy P P' with hlt | heq | hgt
  · exact Or.inl hlt
  · subst heq
    exact Or.inr ⟨rfl, by omega⟩
  · exfalso
    have : P' * n + c' < P * n + c := by
      calc P' * n + c' < P' * n + n := by omega
        _ = (P' + 1) * n := by ring
        _ ≤ P * n := Nat.mul_le_mul_right _ hgt
        _ ≤ P * n + c := Nat.le_add_right _ _
    omega

theorem mono_aux2 {P P' c c' n : ℕ} (hc : c < n) (h : P < P' ∨ (P = P' ∧ c < c')) :
    P * n + c < P' * n + c' := by
  rcases h with hlt | ⟨rfl, hlt⟩
  · calc P * n + c < P * n + n := by omega
      _ = (P + 1) * n := by ring
      _ ≤ P' * n := Nat.mul_le_mul_right _ hlt
      _ ≤ P' * n + c' := Nat.le_add_right _ _
  · omega

theorem lin_inj {a b a' b' n : ℕ} (hb : b < n) (hb' : b' < n) (h : a * n + b = a' * n + b') :
    a = a' ∧ b = b' := by
  have h1 : (a * n + b) / n = (a' * n + b') / n := by rw [h]
  have h2 : (a * n + b) % n = (a' * n + b') % n := by rw [h]
  rw [div_lin _ _ _ hb, div_lin _ _ _ hb'] at h1
  rw [mod_lin _ _ _ hb, mod_lin _ _ _ hb'] at h2
  exact ⟨h1, h2⟩

/-- The lexicographic order on `(a, b, c)`. -/
def Lex3 (a b c a' b' c' : ℕ) : Prop := a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))

theorem lex_L {a b c a' b' c' d q N1 N2 : ℕ} (hq : 0 < q) (hd : d < q) (hb : b < N1)
    (hb' : b' < N1) (hc : c < N2) (hc' : c' < N2) :
    ((a * N1 + b) * q + d) * N2 + c < ((a' * N1 + b') * q + d) * N2 + c' ↔ Lex3 a b c a' b' c' := by
  constructor
  · intro h
    rcases mono_aux hc hc' h with h1 | ⟨h1, h2⟩
    · have h3 : a * N1 + b < a' * N1 + b' := by
        have : (a * N1 + b) * q < (a' * N1 + b') * q := by omega
        exact Nat.lt_of_mul_lt_mul_right this
      rcases mono_aux hb hb' h3 with h4 | ⟨h4, h5⟩
      · exact Or.inl h4
      · exact Or.inr ⟨h4, Or.inl h5⟩
    · have h3 : a * N1 + b = a' * N1 + b' := by
        have : (a * N1 + b) * q = (a' * N1 + b') * q := by omega
        exact Nat.eq_of_mul_eq_mul_right hq this
      obtain ⟨h4, h5⟩ := lin_inj hb hb' h3
      exact Or.inr ⟨h4, Or.inr ⟨h5, h2⟩⟩
  · intro h
    refine mono_aux2 hc ?_
    rcases h with h1 | ⟨rfl, h1 | ⟨rfl, h2⟩⟩
    · left
      have h3 : a * N1 + b < a' * N1 + b' := mono_aux2 hb (Or.inl h1)
      have : (a * N1 + b) * q < (a' * N1 + b') * q := Nat.mul_lt_mul_of_pos_right h3 hq
      omega
    · left
      have h3 : a * N1 + b < a * N1 + b' := by omega
      have : (a * N1 + b) * q < (a * N1 + b') * q := Nat.mul_lt_mul_of_pos_right h3 hq
      omega
    · exact Or.inr ⟨rfl, h2⟩

theorem lex_R {a b c a' b' c' d q N1 N2 : ℕ} (hq : 0 < q) (hd : d < q) (hb : b < N1)
    (hb' : b' < N1) (hc : c < N2) (hc' : c' < N2) :
    ((a * q + d) * N1 + b) * N2 + c < ((a' * q + d) * N1 + b') * N2 + c' ↔ Lex3 a b c a' b' c' := by
  constructor
  · intro h
    rcases mono_aux hc hc' h with h1 | ⟨h1, h2⟩
    · rcases mono_aux hb hb' h1 with h4 | ⟨h4, h5⟩
      · have : a * q < a' * q := by omega
        exact Or.inl (Nat.lt_of_mul_lt_mul_right this)
      · have : a * q = a' * q := by omega
        exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hq this, Or.inl h5⟩
    · obtain ⟨h4, h5⟩ := lin_inj hb hb' h1
      have : a * q = a' * q := by omega
      exact Or.inr ⟨Nat.eq_of_mul_eq_mul_right hq this, Or.inr ⟨h5, h2⟩⟩
  · intro h
    refine mono_aux2 hc ?_
    rcases h with h1 | ⟨rfl, h1 | ⟨rfl, h2⟩⟩
    · left
      refine mono_aux2 hb (Or.inl ?_)
      have : a * q < a' * q := Nat.mul_lt_mul_of_pos_right h1 hq
      omega
    · left
      exact mono_aux2 hb (Or.inr ⟨rfl, h1⟩)
    · exact Or.inr ⟨rfl, h2⟩

/-! ## Decompositions -/

/-- Decomposition in the layout `[·] × [N1] × [q] × [N2]`. -/
theorem decompR (q N1 N2 y : ℕ) :
    y = ((y / (N2 * q * N1) * N1 + y / (N2 * q) % N1) * q + y / N2 % q) * N2 + y % N2 := by
  have h1 := Nat.div_add_mod' y N2
  have h2 := Nat.div_add_mod' (y / N2) q
  have h3 := Nat.div_add_mod' (y / N2 / q) N1
  simp only [Nat.div_div_eq_div_mul] at h2 h3
  rw [h3, h2, h1]

/-- Decomposition in the layout `[·] × [q] × [N1] × [N2]`. -/
theorem decompL (q N1 N2 y : ℕ) :
    y = ((y / (N2 * N1 * q) * q + y / (N2 * N1) % q) * N1 + y / N2 % N1) * N2 + y % N2 := by
  have h1 := Nat.div_add_mod' y N2
  have h2 := Nat.div_add_mod' (y / N2) N1
  have h3 := Nat.div_add_mod' (y / N2 / N1) q
  simp only [Nat.div_div_eq_div_mul] at h2 h3
  rw [h3, h2, h1]

/-! ## The two nests -/

/-- Nest of the layout `[·] × [q] × [N1] × [N2]`. -/
def mdA : List NLab := [.A, .R 0, .R 1]

/-- Nest of the layout `[·] × [N1] × [q] × [N2]`. -/
def mdB : List NLab := [.R 0, .A, .R 1]

/-- Stream selector: only the moved digit. -/
def selM {q : ℕ} [NeZero q] (κ : Key q) : Key q := (κ.1, 0)

theorem mdA_size (q N1 N2 : ℕ) : sizeN q (nsOf N1 N2) mdA = q * (N1 * (N2 * 1)) := by
  simp [mdA, sizeN, NLab.size, nsOf]

theorem mdB_size (q N1 N2 : ℕ) : sizeN q (nsOf N1 N2) mdB = N1 * (q * (N2 * 1)) := by
  simp [mdB, sizeN, NLab.size, nsOf]

theorem mdA_key (q N1 N2 : ℕ) [NeZero q] (κ : Key q) (x : ℕ) :
    selM (keyN q (nsOf N1 N2) mdA κ (x % sizeN q (nsOf N1 N2) mdA)) =
      (modFin q (x / (N2 * N1)), 0) := by
  rw [mdA_size]
  simp only [mdA, keyN, sizeN, NLab.size, nsOf, updN, selM]
  simp only [show ((0 : Fin 2).val = 0) from rfl, show ((1 : Fin 2).val = 0) = False by decide,
    if_true, if_false]
  ext
  · simp only [Fin.val_ofNat, modFin]
    rw [Nat.mod_mul_left_div_self, Nat.mod_mod, show N1 * (N2 * 1) = N2 * N1 by ring]
  · rfl

theorem mdB_key (q N1 N2 : ℕ) [NeZero q] (κ : Key q) (y : ℕ) :
    selM (keyN q (nsOf N1 N2) mdB κ (y % sizeN q (nsOf N1 N2) mdB)) = (modFin q (y / N2), 0) := by
  rw [mdB_size]
  simp only [mdB, keyN, sizeN, NLab.size, nsOf, updN, selM]
  simp only [show ((0 : Fin 2).val = 0) from rfl, show ((1 : Fin 2).val = 0) = False by decide,
    if_true, if_false]
  ext
  · simp only [Fin.val_ofNat, modFin]
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left N1 (show N1 * (q * (N2 * 1)) =
        N1 * (q * (N2 * 1)) from rfl)),
      show q * (N2 * 1) = q * N2 by ring, Nat.mul_one, Nat.mod_mul_left_div_self, Nat.mod_mod]
  · rfl

/-! ## The address maps -/

section Maps

variable (q N1 N2 : ℕ) [NeZero q]

theorem mr_lt (N0 y : ℕ) (hy : y < N0 * q * N1 * N2) :
    moveRightMixInv q N1 N2 y < N0 * q * N1 * N2 := by
  have hpos : 0 < N0 * q * N1 * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hN2 : 0 < N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hN1 : 0 < N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hq : 0 < q := Nat.pos_of_neZero q
  have hk : 0 < N2 * q * N1 := by positivity
  have ha : y / (N2 * q * N1) < N0 := by
    rw [Nat.div_lt_iff_lt_mul hk]
    calc y < N0 * q * N1 * N2 := hy
      _ = N0 * (N2 * q * N1) := by ring
  exact lin_lt (lin_lt (lin_lt ha (Nat.mod_lt _ hq)) (Nat.mod_lt _ hN1)) (Nat.mod_lt _ hN2)

theorem mr_key (y : ℕ) (hN1 : 0 < N1) (hN2 : 0 < N2) :
    ((modFin q (moveRightMixInv q N1 N2 y / (N2 * N1)), 0) : Key q) = (modFin q (y / N2), 0) := by
  have hq : 0 < q := Nat.pos_of_neZero q
  ext
  · simp only [modFin_val, moveRightMixInv]
    rw [← Nat.div_div_eq_div_mul, div_lin _ _ _ (Nat.mod_lt _ hN2),
      div_lin _ _ _ (Nat.mod_lt _ hN1), mod_lin _ _ _ (Nat.mod_lt _ hq)]
  · rfl

theorem mr_mono (y y' : ℕ) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (he : ((modFin q (y / N2), 0) : Key q) = (modFin q (y' / N2), 0)) (hlt : y < y') :
    moveRightMixInv q N1 N2 y < moveRightMixInv q N1 N2 y' := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hd : y / N2 % q = y' / N2 % q := by
    have := congrArg (fun κ : Key q => κ.1.val) he
    simpa [modFin_val] using this
  have hy := decompR q N1 N2 y
  have hy' := decompR q N1 N2 y'
  rw [hd] at hy
  have hL : ((y / (N2 * q * N1) * N1 + y / (N2 * q) % N1) * q + y' / N2 % q) * N2 + y % N2 <
      ((y' / (N2 * q * N1) * N1 + y' / (N2 * q) % N1) * q + y' / N2 % q) * N2 + y' % N2 := by
    rw [← hy, ← hy']; exact hlt
  have hlex := (lex_L hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN1)
    (Nat.mod_lt _ hN2) (Nat.mod_lt _ hN2)).1 hL
  have hR := (lex_R (d := y' / N2 % q) hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hN1)
    (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN2) (Nat.mod_lt _ hN2)).2 hlex
  simp only [moveRightMixInv]
  rw [hd]
  exact hR

theorem ml_lt (N0 y : ℕ) (hy : y < N0 * q * N1 * N2) :
    moveLeftMixInv q N1 N2 y < N0 * q * N1 * N2 := by
  have hpos : 0 < N0 * q * N1 * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  have hN2 : 0 < N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hN1 : 0 < N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hpos)
  have hq : 0 < q := Nat.pos_of_neZero q
  have hk : 0 < N2 * N1 * q := by positivity
  have ha : y / (N2 * N1 * q) < N0 := by
    rw [Nat.div_lt_iff_lt_mul hk]
    calc y < N0 * q * N1 * N2 := hy
      _ = N0 * (N2 * N1 * q) := by ring
  have h := lin_lt (lin_lt (lin_lt ha (Nat.mod_lt (y / N2) hN1)) (Nat.mod_lt (y / (N2 * N1)) hq))
    (Nat.mod_lt y hN2)
  calc moveLeftMixInv q N1 N2 y < N0 * N1 * q * N2 := h
    _ = N0 * q * N1 * N2 := by ring

theorem ml_key (y : ℕ) (hN1 : 0 < N1) (hN2 : 0 < N2) :
    ((modFin q (moveLeftMixInv q N1 N2 y / N2), 0) : Key q) = (modFin q (y / (N2 * N1)), 0) := by
  have hq : 0 < q := Nat.pos_of_neZero q
  ext
  · simp only [modFin_val, moveLeftMixInv]
    rw [div_lin _ _ _ (Nat.mod_lt _ hN2), mod_lin _ _ _ (Nat.mod_lt _ hq)]
  · rfl

theorem ml_mono (y y' : ℕ) (hN1 : 0 < N1) (hN2 : 0 < N2)
    (he : ((modFin q (y / (N2 * N1)), 0) : Key q) = (modFin q (y' / (N2 * N1)), 0))
    (hlt : y < y') : moveLeftMixInv q N1 N2 y < moveLeftMixInv q N1 N2 y' := by
  have hq : 0 < q := Nat.pos_of_neZero q
  have hd : y / (N2 * N1) % q = y' / (N2 * N1) % q := by
    have := congrArg (fun κ : Key q => κ.1.val) he
    simpa [modFin_val] using this
  have hy := decompL q N1 N2 y
  have hy' := decompL q N1 N2 y'
  rw [hd] at hy
  have hR : ((y / (N2 * N1 * q) * q + y' / (N2 * N1) % q) * N1 + y / N2 % N1) * N2 + y % N2 <
      ((y' / (N2 * N1 * q) * q + y' / (N2 * N1) % q) * N1 + y' / N2 % N1) * N2 + y' % N2 := by
    rw [← hy, ← hy']; exact hlt
  have hlex := (lex_R hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN1)
    (Nat.mod_lt _ hN2) (Nat.mod_lt _ hN2)).1 hR
  have hL := (lex_L (d := y' / (N2 * N1) % q) hq (Nat.mod_lt _ hq) (Nat.mod_lt _ hN1)
    (Nat.mod_lt _ hN1) (Nat.mod_lt _ hN2) (Nat.mod_lt _ hN2)).2 hlex
  simp only [moveLeftMixInv]
  rw [hd]
  exact hL

end Maps
/-! ## Cost bookkeeping -/

theorem mixCost (v : List (List Bool)) (M0 Bs o1 o2 K : ℕ) (hlen : v.length = M0 * Bs)
    (ho : M0 ≠ 0 → o1 + 1 ≤ 1679616 * Bs ∧ o2 + 1 ≤ 1679616 * Bs) :
    6 * vol v + 2 * K * v.length + M0 * (o1 + o2 + 5) + 5 ≤
      (2 * 1679616 + 2 * K + 9) * (vol v + 1) := by
  have hvl := length_le_vol v
  have hK : M0 * (o1 + o2 + 5) ≤ (2 * 1679616 + 3) * v.length := by
    by_cases h0 : M0 = 0
    · simp [h0]
    · obtain ⟨h1, h2⟩ := ho h0
      have hBpos : 0 < Bs := by
        rcases Nat.eq_zero_or_pos Bs with h | h
        · rw [h] at h1; omega
        · exact h
      rw [hlen]
      have hM0B : M0 ≤ M0 * Bs := Nat.le_mul_of_pos_right _ hBpos
      have h3 := Nat.mul_le_mul_left M0 h1
      have h4 := Nat.mul_le_mul_left M0 h2
      nlinarith
  have h1 := Nat.mul_le_mul_left (2 * K) hvl
  have h2 := Nat.mul_le_mul_left (2 * 1679616 + 3) hvl
  nlinarith

theorem oh3_le {q : ℕ} (Ns : Fin 2 → ℕ) (D : List NLab) (hD : D.length = 3)
    (hall : ∀ l ∈ D, 1 ≤ l.size q Ns) : ohN q Ns D + 1 ≤ 1679616 * sizeN q Ns D := by
  have h := ohN_le Ns D hall
  rw [hD] at h
  have : 36 ^ 3 * sizeN q Ns D ≤ 1679616 * sizeN q Ns D := Nat.mul_le_mul_right _ (by norm_num)
  omega

/-! ## The contract -/

/-- **[PROVED] K1b-mix**: `K1MoveDigitMixStmt q toRight` holds for every `q` and both directions. -/
theorem k1MoveDigitMix_holds (q : ℕ) (toRight : Bool) : K1MoveDigitMixStmt q toRight := by
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · subst hq0
    refine ⟨1, fun _ => ⟨Empty, inferInstance, inferInstance, Unit, TMFw.Lib.skip, inferInstance,
      inferInstance, ?_, ?_⟩⟩
    · simp [Prog.Closed, Prog.FreeBelow, TMFw.Lib.skip]
    · intro N0 N1 N2 v rest r2 r3 S hlen hrest hr2 hr3 hS hS2 hS3
      have hv : v = [] := List.length_eq_zero_iff.1 (by rw [hlen]; simp)
      subst hv
      have h0 : S (.inl 0) = rest := by simpa [arrSyms, blk] using hS
      have hfin : Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (arrSyms (permByInv (if toRight then moveRightMixInv 0 N1 N2
            else moveLeftMixInv 0 N1 N2) ([] : List (List Bool))) ++ S (.inl 1)) = S := by
        funext x
        by_cases h1 : x = .inl 1
        · subst h1
          simp [permByInv, arrSyms, blk]
        · by_cases h2 : x = .inl 0
          · subst h2
            simp [h0]
          · simp [Function.update_apply, h1, h2]
      rw [hfin]
      have h1 : Runs (TMFw.Lib.skip : Prog (KLoc (Fin 4) Empty) (fun _ => Sym) Unit) S S
          (fun _ => True) 1 :=
        (Triple.load (ρ := []) id (fun s => s.stk = S ∧ True)).pre (fun _ hs => ⟨hs, trivial⟩)
      exact WP.W9comp.runs_mono h1 (fun _ _ => trivial) (by simp [vol, arrSyms, blk])
  have : NeZero q := ⟨by omega⟩
  cases toRight with
  | true =>
    refine ⟨2 * 1679616 + 2 * (allKeys q).length + 9, fun _ => ⟨EM q, inferInstance,
      inferInstance, Reg q, mixProg selM selM mdA mdB, inferInstance, ⟨((none, none, .eq), (0, 0))⟩,
      mixProg_closed _ _ _ _, ?_⟩⟩
    intro N0 N1 N2 v rest r2 r3 S hlen hrest hr2 hr3 hS hS2 hS3
    simp only [if_true]
    set Bs := sizeN q (nsOf N1 N2) mdA with hBs
    have hBs' : Bs = q * (N1 * (N2 * 1)) := mdA_size q N1 N2
    set M0 := if Bs = 0 then 0 else N0 with hM0def
    have hNB : N0 * q * N1 * N2 = N0 * Bs := by rw [hBs']; ring
    have hlen' : v.length = M0 * Bs := by
      rw [hlen, hNB, hM0def]
      by_cases h0 : Bs = 0
      · simp [h0]
      · simp [h0]
    have hM0 : 0 < Bs ∨ M0 = 0 := by
      by_cases h0 : Bs = 0
      · right; simp [hM0def, h0]
      · left; omega
    have hrr : ∀ r : Fin 2, TermOK ((fun r : Fin 2 => if r.val = 0 then r2 else r3) r) := by
      intro r; fin_cases r <;> simp [hr2, hr3]
    have hNP : ∀ r : Fin 2, S (mNP r) = natSyms (nsOf N1 N2 r) ++
        (fun r : Fin 2 => if r.val = 0 then r2 else r3) r := by
      intro r; fin_cases r
      · simpa [mNP, nsOf] using hS2
      · simpa [mNP, nsOf] using hS3
    have hpos : ∀ y, y < v.length → 0 < N1 ∧ 0 < N2 := by
      intro y hy
      rw [hlen] at hy
      have hp : 0 < N0 * q * N1 * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
      exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at hp),
        Nat.pos_of_ne_zero (fun h => by simp [h] at hp)⟩
    have hsz : sizeN q (nsOf N1 N2) mdB = sizeN q (nsOf N1 N2) mdA := by
      rw [mdA_size, mdB_size]; ring
    have hR := mixProg_runs selM selM mdA mdB (nsOf N1 N2) hsz v M0 hlen' hM0
      (fun x => (modFin q (x / (N2 * N1)), 0)) (fun y => (modFin q (y / N2), 0))
      (moveRightMixInv q N1 N2)
      (fun κ x _ => mdA_key q N1 N2 κ x) (fun κ y _ => mdB_key q N1 N2 κ y)
      (fun y hy => by rw [hlen] at hy ⊢; exact mr_lt q N1 N2 N0 y hy)
      (fun y hy => mr_key q N1 N2 y (hpos y hy).1 (hpos y hy).2)
      (fun y y' hy hy' he hlt => mr_mono q N1 N2 y y' (hpos y hy).1 (hpos y hy).2 he hlt)
      rest hrest _ hrr S hS hNP
    refine WP.W9comp.runs_mono hR (fun _ _ => trivial) ?_
    refine mixCost v M0 Bs _ _ _ hlen' (fun h0 => ?_)
    have hBpos : 0 < Bs := by
      rcases hM0 with h | h
      · exact h
      · exact absurd h h0
    rw [hBs'] at hBpos
    have hq : 1 ≤ q := Nat.pos_of_neZero q
    have hN1 : 1 ≤ N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
    have hN2 : 1 ≤ N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
    have hallA : ∀ l ∈ mdA, 1 ≤ l.size q (nsOf N1 N2) := by
      intro l hl
      simp only [mdA, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [NLab.size, nsOf, hq, hN1, hN2]
    have hallB : ∀ l ∈ mdB, 1 ≤ l.size q (nsOf N1 N2) := by
      intro l hl
      simp only [mdB, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [NLab.size, nsOf, hq, hN1, hN2]
    refine ⟨oh3_le _ mdA rfl hallA, ?_⟩
    rw [hBs, ← hsz]
    exact oh3_le _ mdB rfl hallB
  | false =>
    refine ⟨2 * 1679616 + 2 * (allKeys q).length + 9, fun _ => ⟨EM q, inferInstance,
      inferInstance, Reg q, mixProg selM selM mdB mdA, inferInstance, ⟨((none, none, .eq), (0, 0))⟩,
      mixProg_closed _ _ _ _, ?_⟩⟩
    intro N0 N1 N2 v rest r2 r3 S hlen hrest hr2 hr3 hS hS2 hS3
    simp only [Bool.false_eq_true, if_false]
    set Bs := sizeN q (nsOf N1 N2) mdB with hBs
    have hBs' : Bs = N1 * (q * (N2 * 1)) := mdB_size q N1 N2
    set M0 := if Bs = 0 then 0 else N0 with hM0def
    have hNB : N0 * q * N1 * N2 = N0 * Bs := by rw [hBs']; ring
    have hlen' : v.length = M0 * Bs := by
      rw [hlen, hNB, hM0def]
      by_cases h0 : Bs = 0
      · simp [h0]
      · simp [h0]
    have hM0 : 0 < Bs ∨ M0 = 0 := by
      by_cases h0 : Bs = 0
      · right; simp [hM0def, h0]
      · left; omega
    have hrr : ∀ r : Fin 2, TermOK ((fun r : Fin 2 => if r.val = 0 then r2 else r3) r) := by
      intro r; fin_cases r <;> simp [hr2, hr3]
    have hNP : ∀ r : Fin 2, S (mNP r) = natSyms (nsOf N1 N2 r) ++
        (fun r : Fin 2 => if r.val = 0 then r2 else r3) r := by
      intro r; fin_cases r
      · simpa [mNP, nsOf] using hS2
      · simpa [mNP, nsOf] using hS3
    have hpos : ∀ y, y < v.length → 0 < N1 ∧ 0 < N2 := by
      intro y hy
      rw [hlen] at hy
      have hp : 0 < N0 * q * N1 * N2 := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
      exact ⟨Nat.pos_of_ne_zero (fun h => by simp [h] at hp),
        Nat.pos_of_ne_zero (fun h => by simp [h] at hp)⟩
    have hsz : sizeN q (nsOf N1 N2) mdA = sizeN q (nsOf N1 N2) mdB := by
      rw [mdA_size, mdB_size]; ring
    have hR := mixProg_runs selM selM mdB mdA (nsOf N1 N2) hsz v M0 hlen' hM0
      (fun x => (modFin q (x / N2), 0)) (fun y => (modFin q (y / (N2 * N1)), 0))
      (moveLeftMixInv q N1 N2)
      (fun κ x _ => mdB_key q N1 N2 κ x) (fun κ y _ => mdA_key q N1 N2 κ y)
      (fun y hy => by rw [hlen] at hy ⊢; exact ml_lt q N1 N2 N0 y hy)
      (fun y hy => ml_key q N1 N2 y (hpos y hy).1 (hpos y hy).2)
      (fun y y' hy hy' he hlt => ml_mono q N1 N2 y y' (hpos y hy).1 (hpos y hy).2 he hlt)
      rest hrest _ hrr S hS hNP
    refine WP.W9comp.runs_mono hR (fun _ _ => trivial) ?_
    refine mixCost v M0 Bs _ _ _ hlen' (fun h0 => ?_)
    have hBpos : 0 < Bs := by
      rcases hM0 with h | h
      · exact h
      · exact absurd h h0
    rw [hBs'] at hBpos
    have hq : 1 ≤ q := Nat.pos_of_neZero q
    have hN1 : 1 ≤ N1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
    have hN2 : 1 ≤ N2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hBpos)
    have hallA : ∀ l ∈ mdA, 1 ≤ l.size q (nsOf N1 N2) := by
      intro l hl
      simp only [mdA, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [NLab.size, nsOf, hq, hN1, hN2]
    have hallB : ∀ l ∈ mdB, 1 ≤ l.size q (nsOf N1 N2) := by
      intro l hl
      simp only [mdB, List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl <;> simp [NLab.size, nsOf, hq, hN1, hN2]
    refine ⟨oh3_le _ mdB rfl hallB, ?_⟩
    rw [hBs, ← hsz]
    exact oh3_le _ mdA rfl hallA

end SubNLogN.Machine.K1Digit
