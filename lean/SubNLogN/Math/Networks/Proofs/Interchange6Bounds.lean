import SubNLogN.Math.Networks.Proofs.Interchange6Binary
import SubNLogN.Math.Networks.Proofs.Interchange6Common
import SubNLogN.Math.Networks.Proofs.Counting
import SubNLogN.S1.Params

/-!
# The Lemma A.8 (`lem:transfer12`) arithmetic interface

The reshape and parameter facts behind the Lemma A.8 (`lem:transfer12`) procedure of `AppCProc6.lean`
(Lemma A.8 (`lem:transfer12`), Appendix A.3 (`sec:transfer-arbitrary`),
reshape injectivity and parameter bounds):
* `recodeAddr_injective`: a recoding is injective when the old block range is at most `r'^len'`;
* `restrict_embed`, `embed_permutation_transport`: restriction after embedding along an injective map,
  also after a pair of permutations commuting with the map;
* `ic6_parameters`: the integers `k = ic6K len`, `t = ic6T q len`, `R = ic6R q len` of the q-ary
  procedure, for every `q ≥ 2` and every `len ≥ m = mH`. These are `1 ≤ k`, `1 ≤ t ≤ 68k`,
  `t < len`, `W_b^k ≤ q^t ≤ R < 2 q^t` and `W_b^k ∣ R`. The threshold is the exact condition `mH ≤ len`;
  the constant `68` comes from `W_b < 2^68` (`W_b = tripleWb 100 = 177176569091445000000`);
* `binDigits_bounds`: `e = binDigits q u` satisfies `1 ≤ e ≤ u` and `2^u ≤ q^e < q·2^u` (`q ≥ 2`,
  `u ≥ 1`), so padding both binary coordinates enlarges the volume by a factor `< q^2`;
* `interchangeProc_zero_top`: the depth-`0` Proposition A.7 (`prop:transfer11`) procedure run in any top class is the one-field
  interchange; there is no hypothesis relating the row field to the swapped fields.
-/

namespace SubNLogN.Math.Networks

open Model

namespace Interchange6BoundsAux

/-- `mH = 10^6`. -/
theorem mH_eq : mH = 1000000 := by norm_num [mH]

/-- `W_b = tripleWb 100 = 177176569091445000000`. -/
theorem Wb_eq : Wb = 177176569091445000000 := by
  show Fintype.card (Role .bit 100) = _
  rw [(cardRole_holds 100).1, SubNLogN.S1.tripleWb_100]

/-- `W_b < 2^68`. -/
theorem Wb_lt : Wb < 2 ^ 68 := by
  rw [Wb_eq]; norm_num

/-- `2 ≤ W_b`. -/
theorem two_le_Wb : 2 ≤ Wb := by
  rw [Wb_eq]; norm_num

/-- `68 (j + 2) ≤ m^(j+1)`, i.e. `68 k ≤ m^(k-1)` for `k ≥ 2`. -/
theorem sixtyeight_mul_le_pow (j : ℕ) : 68 * (j + 2) ≤ mH ^ (j + 1) := by
  induction j with
  | zero => rw [mH_eq]; norm_num
  | succ j ih =>
    rw [pow_succ]
    rw [mH_eq] at ih ⊢
    have h1 : 1 ≤ 1000000 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    generalize 1000000 ^ (j + 1) = X at ih h1 ⊢
    omega

/-- `68 k < len` for `k = ic6K len` and `len ≥ m`. -/
theorem sixtyeight_mul_ic6K_lt {len : ℕ} (he : mH ≤ len) : 68 * ic6K len < len := by
  have hm := mH_eq
  rcases Nat.lt_or_ge (ic6K len) 2 with hk | hk
  · have hk1 : ic6K len ≤ 1 := by omega
    rw [hm] at he
    omega
  · obtain ⟨j, hj⟩ : ∃ j, ic6K len = j + 2 := ⟨ic6K len - 2, by omega⟩
    have h1 := sixtyeight_mul_le_pow j
    have h2 : mH ^ (Nat.clog mH len).pred < len :=
      Nat.pow_pred_clog_lt_self (by rw [hm]; norm_num) (by rw [hm] at he; omega)
    have h3 : (Nat.clog mH len).pred = j + 1 := by
      have : Nat.clog mH len = j + 2 := hj
      rw [this]; rfl
    rw [h3] at h2
    rw [hj]
    omega

end Interchange6BoundsAux

open Interchange6BoundsAux

/-- A recoding is injective when the old block range is at most `r' ^ len'`
(re-export of `Interchange6BinAux.recodeAddr_injective`). -/
theorem recodeAddr_injective {L : Layout} {t len r' len' : ℕ} (hr : 0 < r') (ht : t + len ≤ L.n)
    (hle : L.blockRange t (t + len) ≤ r' ^ len') :
    Function.Injective (recodeAddr L t len r' len' hr ht) :=
  Interchange6BinAux.recodeAddr_injective hr ht hle

/-- Restricting along an injective map undoes embedding along it. -/
theorem restrict_embed {L L' : Layout} {β : Type} [Zero β] (f : L.Addr → L'.Addr)
    (hf : Function.Injective f) (A : L.Addr → β) : restrictAlong f (embedAlong f A) = A :=
  Interchange6Aux.restrictAlong_embedAlong hf A

/-- Embedding, permuting by `q`, and restricting is permuting by `p`, when `f ∘ p = q ∘ f`. -/
theorem embed_permutation_transport {L L' : Layout} {γ : Type} [Zero γ] (f : L.Addr → L'.Addr)
    (hf : Function.Injective f) (p : Equiv.Perm L.Addr) (q : Equiv.Perm L'.Addr)
    (hcomm : ∀ x, f (p x) = q (f x)) (A : L.Addr → γ) :
    restrictAlong f ((embedAlong f A) ∘ q.symm) = A ∘ p.symm := by
  funext x
  simp only [restrictAlong, Function.comp]
  have h1 : q.symm (f x) = f (p.symm x) := by
    rw [Equiv.symm_apply_eq, ← hcomm, Equiv.apply_symm_apply]
  rw [h1, Interchange6Aux.embedAlong_apply hf]

/-- **The Lemma A.8 (`lem:transfer12`) parameters**: for `q ≥ 2` and `len ≥ m`, with `k = ic6K len`,
`t = ic6T q len`, `R = ic6R q len`: `1 ≤ k`, `1 ≤ t ≤ 68k`, `t < len`, `W_b^k ≤ q^t ≤ R < 2q^t` and
`W_b^k ∣ R`. -/
theorem ic6_parameters {q len : ℕ} (hq : 2 ≤ q) (he : mH ≤ len) :
    1 ≤ ic6K len ∧ 1 ≤ ic6T q len ∧ ic6T q len ≤ 68 * ic6K len ∧ ic6T q len < len ∧
      Wb ^ ic6K len ≤ q ^ ic6T q len ∧ q ^ ic6T q len ≤ ic6R q len ∧
      ic6R q len < 2 * q ^ ic6T q len ∧ Wb ^ ic6K len ∣ ic6R q len := by
  have hm := mH_eq
  have hk1 : 1 ≤ ic6K len :=
    Nat.clog_pos (by rw [hm]; norm_num) (by rw [hm] at he; omega)
  have hWk : 2 ≤ Wb ^ ic6K len :=
    le_trans two_le_Wb (Nat.le_self_pow (by omega) Wb)
  have ht1 : 1 ≤ ic6T q len := Nat.clog_pos (by omega) (by omega)
  have hWq : Wb ^ ic6K len ≤ q ^ ic6T q len := Nat.le_pow_clog (by omega) _
  have ht68 : ic6T q len ≤ 68 * ic6K len := by
    show Nat.clog q (Wb ^ ic6K len) ≤ 68 * ic6K len
    apply Nat.clog_le_of_le_pow
    calc Wb ^ ic6K len ≤ (2 ^ 68) ^ ic6K len := Nat.pow_le_pow_left (le_of_lt Wb_lt) _
      _ = 2 ^ (68 * ic6K len) := by rw [← pow_mul]
      _ ≤ q ^ (68 * ic6K len) := Nat.pow_le_pow_left hq _
  have hlen := sixtyeight_mul_ic6K_lt he
  refine ⟨hk1, ht1, ht68, by omega, hWq, ?_⟩
  show q ^ ic6T q len ≤ Wb ^ ic6K len * ((q ^ ic6T q len + Wb ^ ic6K len - 1) / Wb ^ ic6K len) ∧
    Wb ^ ic6K len * ((q ^ ic6T q len + Wb ^ ic6K len - 1) / Wb ^ ic6K len) < 2 * q ^ ic6T q len ∧
    Wb ^ ic6K len ∣ Wb ^ ic6K len * ((q ^ ic6T q len + Wb ^ ic6K len - 1) / Wb ^ ic6K len)
  generalize Wb ^ ic6K len = W at hWk hWq ⊢
  generalize q ^ ic6T q len = Q at hWq ⊢
  have h1 := Nat.div_add_mod (Q + W - 1) W
  have h2 := Nat.mod_lt (Q + W - 1) (show 0 < W by omega)
  exact ⟨by omega, by omega, Dvd.intro _ rfl⟩

/-- **Binary padding digits**: `e = binDigits q u` satisfies `1 ≤ e ≤ u` and
`2^u ≤ q^e < q · 2^u` for `q ≥ 2`, `u ≥ 1`. -/
theorem binDigits_bounds {q u : ℕ} (hq : 2 ≤ q) (hu : 1 ≤ u) :
    1 ≤ binDigits q u ∧ binDigits q u ≤ u ∧ 2 ^ u ≤ q ^ binDigits q u ∧
      q ^ binDigits q u < q * 2 ^ u := by
  have h2u : 2 ≤ 2 ^ u := Nat.le_self_pow (by omega) 2
  have he1 : 1 ≤ binDigits q u := Nat.clog_pos (by omega) (by omega)
  have heu : binDigits q u ≤ u := Nat.clog_le_of_le_pow (Nat.pow_le_pow_left hq u)
  have hle : 2 ^ u ≤ q ^ binDigits q u := Nat.le_pow_clog (by omega) _
  have hlt : q ^ (binDigits q u).pred < 2 ^ u := Nat.pow_pred_clog_lt_self (by omega) (by omega)
  refine ⟨he1, heu, hle, ?_⟩
  obtain ⟨d, hd⟩ : ∃ d, binDigits q u = d + 1 := ⟨binDigits q u - 1, by omega⟩
  rw [hd] at hlt ⊢
  rw [pow_succ]
  calc q ^ d * q = q * q ^ d := mul_comm _ _
    _ < q * 2 ^ u := Nat.mul_lt_mul_of_pos_left hlt (by omega)

/-- **The depth-`0` Proposition A.7 (`prop:transfer11`) procedure in a top class**: one digit swap is the one-field
interchange `swapBlocks h₀ d₀ 1`, for any row field (no condition `row < h₀`). -/
theorem interchangeProc_zero_top {L : Layout} {β : Type} [AddCommGroup β] [Module (ZMod 2) β]
    (q : ℕ) (fac : Matrix (Fin mH) (Fin mH) ℚ → FacData) {h₀ d₀ : ℕ} (h : TwoBlocks L q 1 h₀ d₀)
    (row : Fin L.n) (A : L.Addr → β) :
    ProcK.run 0 (interchangeProc (L := L) (β := β) q fac 0 h₀ d₀) (RowClass.top row) A =
      (Step.swapBlocks h₀ d₀ 1 : Step L β).run A := by
  have h1 : h₀ < d₀ := by have := h.1; omega
  have h2 : d₀ < L.n := by have := h.2.1; omega
  have hr : L.r ⟨h₀, by omega⟩ = L.r ⟨d₀, h2⟩ := by
    rw [h.2.2 ⟨h₀, by omega⟩ (Or.inl ⟨le_refl _, by simp⟩),
      h.2.2 ⟨d₀, h2⟩ (Or.inr ⟨le_refl _, by simp⟩)]
  rw [Interchange6Aux.run_interchangeProc_zero q fac h1 h2 hr row A]
  rfl

end SubNLogN.Math.Networks
