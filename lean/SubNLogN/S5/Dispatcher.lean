import SubNLogN.Spec
import SubNLogN.S1.Contracts
import SubNLogN.S2.Contracts
import SubNLogN.S3.Contracts
import SubNLogN.S4.Contracts
import SubNLogN.S5.Schedule
import IntMulTM.Headline

/-!
# Component S5 (`Dispatcher.lean`): Exponent Monotonicity, `o(n log n)` & Top-Level `TM2` Assembly

Proves:
1. Equivalence between `IntMulTM.PairSym` / `IntMulTM.encNatPair` and `SubNLogN.PairSym` /
   `SubNLogN.encNatPair`;
2. Monotonicity of `IntMulSubNLogN` in `κ_exp`:
   `κ₁ ≤ κ₂ → IntMulSubNLogN κ₁ → IntMulSubNLogN κ₂`;
3. Deduction of `Headline_TM2_LittleO_NLogN` from `IntMulSubNLogN 46`;
4. Compiler bridge `W12_subNLogN_assembly_holds` (`TMFw.Prog` → `IntMulSubNLogN κ_exp`; unconditional
   discharge of `Headline_TM2_SubNLogN_46`, `_47`, `_56` lives in `S5/TopObligation.lean`).
-/

namespace SubNLogN.S5

open SubNLogN Computability

/-- Equivalence between the 3-symbol input alphabets `IntMulTM.PairSym` and `SubNLogN.PairSym`. -/
def pairSymEquiv : IntMulTM.PairSym ≃ SubNLogN.PairSym where
  toFun
    | .bit b => .bit b
    | .sep => .sep
  invFun
    | .bit b => .bit b
    | .sep => .sep
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

theorem encodeNatPair_eq_map_pairSymEquiv (p : ℕ × ℕ) :
    SubNLogN.encNatPair.encode p = (IntMulTM.encNatPair.encode p).map pairSymEquiv := by
  simp only [SubNLogN.encNatPair, SubNLogN.encodeNatPair, IntMulTM.encNatPair,
    IntMulTM.encodeNatPair, List.map_append, List.map_map, List.map_cons]
  rfl

theorem encodeNatPair_length_eq (p : ℕ × ℕ) :
    (SubNLogN.encNatPair.encode p).length = (IntMulTM.encNatPair.encode p).length := by
  rw [encodeNatPair_eq_map_pairSymEquiv, List.length_map]

/-- **Base `O(L log₂ L)` `TM2` Multiplier (`Remark 7.4`, `rem:crt-free` / `IntMulTM.intMul_TM2_nlogn`):**
The unconditional `O(L log₂ L)` multi-stack Turing machine from `IntMulTM.Headline`, transported
along `pairSymEquiv` to `SubNLogN.encNatPair`. Used as the fallback multiplier below the cutoff
`n_*` and as the delegated leaf multiplier for `O(P)`- and `O(P^2)`-bit integer products inside the
`d`-dimensional bridge (`Theorem 1` / `Theorem 2` & `Remark 7.4`). -/
theorem intMul_TM2_nlogn_subNLogNSpec :
    ∃ M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
        (fun p : ℕ × ℕ => p.1 * p.2),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∃ C N₀ : ℕ, 0 < C ∧ ∀ L ≥ N₀, M.time L ≤ C * L * Nat.log2 L := by
  obtain ⟨M₀, hfin₀, C₀, N₀, hT₀⟩ := IntMulTM.intMul_TM2_nlogn
  let M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
      (fun p : ℕ × ℕ => p.1 * p.2) :=
    { tm := M₀.tm
      inputAlphabet := M₀.inputAlphabet.trans pairSymEquiv
      outputAlphabet := M₀.outputAlphabet
      time := M₀.time
      outputsFun := fun p => by
        have hmap : List.map (M₀.inputAlphabet.trans pairSymEquiv).invFun (encNatPair.encode p) =
            List.map M₀.inputAlphabet.invFun (IntMulTM.encNatPair.encode p) := by
          rw [encodeNatPair_eq_map_pairSymEquiv, List.map_map]
          congr 1
          funext x
          simp [Equiv.trans]
        rw [hmap, encodeNatPair_length_eq]
        exact M₀.outputsFun p }
  refine ⟨M, hfin₀, C₀ + 1, N₀, Nat.succ_pos C₀, fun L hL => ?_⟩
  have h1 := hT₀ L hL
  have h2 : C₀ * L * Nat.log2 L ≤ (C₀ + 1) * L * Nat.log2 L :=
    Nat.mul_le_mul_right (Nat.log2 L) (Nat.mul_le_mul_right L (Nat.le_succ C₀))
  exact le_trans h1 h2

/-- **Transport from `IntMulTM.encNatPair` to `SubNLogN.encNatPair` (`transport_TM2_subNLogN`):**
Any `Turing.TM2ComputableInTime` machine over `IntMulTM.encNatPair` satisfying the sub-`n log n`
time bound transports along `pairSymEquiv` (with the identical `tm` and `time` function) to a
witness of `SubNLogN.IntMulSubNLogN κ_exp`. -/
theorem transport_TM2_subNLogN {κ_exp : ℕ}
    (h : ∃ M₀ : Turing.TM2ComputableInTime IntMulTM.encNatPair.encode encodingNatBool.encode
        (fun p : ℕ × ℕ => p.1 * p.2),
      (∀ k, Finite (M₀.tm.Γ k)) ∧
      ∃ C N₀ : ℕ, 0 < C ∧ ∀ L ≥ N₀,
        (M₀.time L) ^ (2 ^ κ_exp) ≤
          (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)) :
    IntMulSubNLogN κ_exp := by
  obtain ⟨M₀, hfin₀, C, N₀, hC, hT⟩ := h
  let M : Turing.TM2ComputableInTime encNatPair.encode encodingNatBool.encode
      (fun p : ℕ × ℕ => p.1 * p.2) :=
    { tm := M₀.tm
      inputAlphabet := M₀.inputAlphabet.trans pairSymEquiv
      outputAlphabet := M₀.outputAlphabet
      time := M₀.time
      outputsFun := fun p => by
        have hmap : List.map (M₀.inputAlphabet.trans pairSymEquiv).invFun (encNatPair.encode p) =
            List.map M₀.inputAlphabet.invFun (IntMulTM.encNatPair.encode p) := by
          rw [encodeNatPair_eq_map_pairSymEquiv, List.map_map]
          congr 1
          funext x
          simp [Equiv.trans]
        rw [hmap, encodeNatPair_length_eq]
        exact M₀.outputsFun p }
  exact ⟨M, hfin₀, C, N₀, hC, hT⟩

instance : Fintype SubNLogN.PairSym :=
  Fintype.ofEquiv IntMulTM.PairSym pairSymEquiv

/-- **Rational Sub-Exponent Bridge (`subexponent_subNLogN`):**
If a stage cost `T` satisfies `(T L)^q ≤ (C · L)^q · (log₂ L)^p` with rational log-exponent
`p / q ≤ 1 - 2^{-κ}`, then `T` satisfies the `IntMulSubNLogN κ` power bound
`(T L)^{2^κ} ≤ (C · L)^{2^κ} · (log₂ L)^{2^κ - 1}` for all `L ≥ max N₀ 2`. -/
theorem subexponent_subNLogN {T : ℕ → ℕ} {p q κ_exp C N₀ : ℕ}
    (hq : 0 < q)
    (hexp : p * 2 ^ κ_exp ≤ q * (2 ^ κ_exp - 1))
    (hT : ∀ L ≥ N₀, (T L) ^ q ≤ (C * L) ^ q * (Nat.log2 L) ^ p) :
    ∀ L ≥ max N₀ 2,
      (T L) ^ (2 ^ κ_exp) ≤ (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1) := by
  intro L hL
  set m := 2 ^ κ_exp
  have hL_N₀ : N₀ ≤ L := le_of_max_le_left hL
  have hL_2 : 2 ≤ L := le_of_max_le_right hL
  have hlog : 1 ≤ Nat.log2 L := (Nat.le_log2 (by omega)).2 (by simpa using hL_2)
  rw [← Nat.pow_le_pow_iff_left (by omega : q ≠ 0)]
  have h1 := Nat.pow_le_pow_left (hT L hL_N₀) m
  have hlog_pow : (Nat.log2 L) ^ (p * m) ≤ (Nat.log2 L) ^ ((m - 1) * q) := by
    apply Nat.pow_le_pow_right hlog
    rw [mul_comm (m - 1) q]
    exact hexp
  calc ((T L) ^ m) ^ q
      = ((T L) ^ q) ^ m := by rw [← pow_mul, mul_comm m q, pow_mul]
    _ ≤ ((C * L) ^ q * (Nat.log2 L) ^ p) ^ m := h1
    _ = ((C * L) ^ m) ^ q * (Nat.log2 L) ^ (p * m) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q m, pow_mul]
    _ ≤ ((C * L) ^ m) ^ q * (Nat.log2 L) ^ ((m - 1) * q) :=
        Nat.mul_le_mul_left _ hlog_pow
    _ = ((C * L) ^ m * (Nat.log2 L) ^ (m - 1)) ^ q := by
        rw [pow_mul (Nat.log2 L), ← mul_pow]

/-- **Sub-`n log n` Cost Addition (`subNLogN_add`):**
If two stage costs `T₁, T₂` satisfy the `IntMulSubNLogN κ` bound with constants `C₁, C₂`,
their sum `T₁ + T₂` satisfies the bound with constant `2 * (C₁ + C₂)`. -/
theorem subNLogN_add {T₁ T₂ : ℕ → ℕ} {κ_exp C₁ C₂ N₁ N₂ : ℕ}
    (h₁ : ∀ L ≥ N₁, (T₁ L) ^ (2 ^ κ_exp) ≤ (C₁ * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1))
    (h₂ : ∀ L ≥ N₂, (T₂ L) ^ (2 ^ κ_exp) ≤ (C₂ * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)) :
    ∀ L ≥ max N₁ N₂,
      (T₁ L + T₂ L) ^ (2 ^ κ_exp) ≤
        ((2 * (C₁ + C₂)) * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1) := by
  intro L hL
  set m := 2 ^ κ_exp
  have hL₁ : N₁ ≤ L := le_of_max_le_left hL
  have hL₂ : N₂ ≤ L := le_of_max_le_right hL
  rcases le_total (T₁ L) (T₂ L) with hle | hle
  · have hsum : T₁ L + T₂ L ≤ 2 * T₂ L := by omega
    have hpow := Nat.pow_le_pow_left hsum m
    have hC : C₂ * L ≤ (C₁ + C₂) * L := Nat.mul_le_mul_right L (by omega)
    have hCpow : (C₂ * L) ^ m * (Nat.log2 L) ^ (m - 1) ≤
        ((C₁ + C₂) * L) ^ m * (Nat.log2 L) ^ (m - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hC m)
    calc (T₁ L + T₂ L) ^ m
        ≤ (2 * T₂ L) ^ m := hpow
      _ = 2 ^ m * (T₂ L) ^ m := mul_pow 2 (T₂ L) m
      _ ≤ 2 ^ m * ((C₂ * L) ^ m * (Nat.log2 L) ^ (m - 1)) := Nat.mul_le_mul_left (2 ^ m) (h₂ L hL₂)
      _ ≤ 2 ^ m * (((C₁ + C₂) * L) ^ m * (Nat.log2 L) ^ (m - 1)) := Nat.mul_le_mul_left (2 ^ m) hCpow
      _ = (2 * ((C₁ + C₂) * L)) ^ m * (Nat.log2 L) ^ (m - 1) := by
          rw [← mul_assoc, ← mul_pow]
      _ = ((2 * (C₁ + C₂)) * L) ^ m * (Nat.log2 L) ^ (m - 1) := by
          rw [mul_assoc 2 (C₁ + C₂) L]
  · have hsum : T₁ L + T₂ L ≤ 2 * T₁ L := by omega
    have hpow := Nat.pow_le_pow_left hsum m
    have hC : C₁ * L ≤ (C₁ + C₂) * L := Nat.mul_le_mul_right L (by omega)
    have hCpow : (C₁ * L) ^ m * (Nat.log2 L) ^ (m - 1) ≤
        ((C₁ + C₂) * L) ^ m * (Nat.log2 L) ^ (m - 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hC m)
    calc (T₁ L + T₂ L) ^ m
        ≤ (2 * T₁ L) ^ m := hpow
      _ = 2 ^ m * (T₁ L) ^ m := mul_pow 2 (T₁ L) m
      _ ≤ 2 ^ m * ((C₁ * L) ^ m * (Nat.log2 L) ^ (m - 1)) := Nat.mul_le_mul_left (2 ^ m) (h₁ L hL₁)
      _ ≤ 2 ^ m * (((C₁ + C₂) * L) ^ m * (Nat.log2 L) ^ (m - 1)) := Nat.mul_le_mul_left (2 ^ m) hCpow
      _ = (2 * ((C₁ + C₂) * L)) ^ m * (Nat.log2 L) ^ (m - 1) := by
          rw [← mul_assoc, ← mul_pow]
      _ = ((2 * (C₁ + C₂)) * L) ^ m * (Nat.log2 L) ^ (m - 1) := by
          rw [mul_assoc 2 (C₁ + C₂) L]

/-- **Absorbing the `+ 1` Wrapper Cleanup Step (`subNLogN_add_one`):**
If `T` satisfies the `IntMulSubNLogN κ` bound with constant `C`, then `T L + 1` satisfies
the bound with constant `2 * (C + 1)` for all `L ≥ max N₀ 2`. -/
theorem subNLogN_add_one {T : ℕ → ℕ} {κ_exp C N₀ : ℕ}
    (hT : ∀ L ≥ N₀, (T L) ^ (2 ^ κ_exp) ≤ (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)) :
    ∀ L ≥ max N₀ 2,
      (T L + 1) ^ (2 ^ κ_exp) ≤
        ((2 * (C + 1)) * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1) := by
  apply subNLogN_add hT
  intro L hL
  have hlog : 1 ≤ Nat.log2 L := (Nat.le_log2 (by omega)).2 (by simpa using hL)
  have hL1 : 1 ≤ 1 * L := by omega
  have h1 : 1 ≤ (1 * L) ^ (2 ^ κ_exp) := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (Nat.log2 L) ^ (2 ^ κ_exp - 1) := Nat.one_le_pow _ _ hlog
  simpa using Nat.mul_le_mul h1 h2

/-- **`W12` Sub-`n log n` Compiler Bridge (`TMFw.Prog` → `IntMulSubNLogN κ_exp`):**
Any closed multi-stack program `P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ`
that computes `(a, b) ↦ encodeNat (a * b)` in source-step bound `T` with
`(T L + 1)^{2^κ} ≤ (C · L)^{2^κ} · (log₂ L)^{2^κ - 1}` compiles via `TMFw.acceptTM` to a finite-
alphabet `Turing.TM2ComputableInTime` machine witnessing `IntMulSubNLogN κ_exp`. -/
def W12_subNLogN_assembly (κ_exp : ℕ) : Prop :=
  ∀ (W σ : Type) [DecidableEq W] [Fintype W] [Fintype σ]
    (P : TMFw.Prog (TMFw.StackId W) (TMFw.StackId.Γ SubNLogN.PairSym) σ) (σ0 : σ) (T : ℕ → ℕ),
    P.Closed →
    (∀ a b : ℕ, TMFw.Triple [] (· = ⟨σ0, TMFw.inputStk (encNatPair.encode (a, b))⟩) P
      (fun s => s.stk = TMFw.outputStk (encodeNat (a * b)))
      (T (encNatPair.encode (a, b)).length)) →
    (∃ C N₀ : ℕ, 0 < C ∧ ∀ L ≥ N₀,
      (T L + 1) ^ (2 ^ κ_exp) ≤
        (C * L) ^ (2 ^ κ_exp) * (Nat.log2 L) ^ (2 ^ κ_exp - 1)) →
    IntMulSubNLogN κ_exp

theorem W12_subNLogN_assembly_holds (κ_exp : ℕ) : W12_subNLogN_assembly κ_exp := by
  intro W σ _ _ _ P σ0 T _ hspec hT
  have hEval : ∀ p : ℕ × ℕ, ∃ v t,
      TMFw.Eval [] P ⟨σ0, TMFw.inputStk (encNatPair.encode p)⟩
        ⟨v, TMFw.outputStk (encodeNat (p.1 * p.2))⟩ t ∧
      t ≤ T (encNatPair.encode p).length := by
    intro p
    obtain ⟨s', t, he, hq, ht⟩ := hspec p.1 p.2 _ rfl
    refine ⟨s'.var, t, ?_, ht⟩
    rw [← hq]
    exact he
  obtain ⟨C, N₀, hC, hbound⟩ := hT
  exact ⟨TMFw.acceptTM encNatPair (fun p => p.1 * p.2) P σ0 T hEval,
    TMFw.acceptTM_finite, C, N₀, hC, hbound⟩

/-- **Monotonicity of `IntMulSubNLogN` in `κ_exp`:**
If a machine satisfies the `O(L (log₂ L)^{1 - 2^{-κ₁}})` bound, then it also satisfies the
`O(L (log₂ L)^{1 - 2^{-κ₂}})` bound for every `κ₂ ≥ κ₁`. -/
theorem intMulSubNLogN_mono {κ₁ κ₂ : ℕ} (hκ : κ₁ ≤ κ₂) (h : IntMulSubNLogN κ₁) :
    IntMulSubNLogN κ₂ := by
  obtain ⟨M, hfin, C, N₀, hC, hT⟩ := h
  refine ⟨M, hfin, C, max N₀ 2, hC, fun L hL => ?_⟩
  have hL_N₀ : N₀ ≤ L := le_of_max_le_left hL
  have hL_2 : 2 ≤ L := le_of_max_le_right hL
  have h1 := hT L hL_N₀
  have hlog : 1 ≤ Nat.log2 L := (Nat.le_log2 (by omega)).2 (by simpa using hL_2)
  set d := κ₂ - κ₁
  have hk_eq : κ₂ = κ₁ + d := (Nat.add_sub_of_le hκ).symm
  have hpow_eq : 2 ^ κ₂ = (2 ^ κ₁) * (2 ^ d) := by rw [hk_eq, pow_add]
  have hpow1 := Nat.pow_le_pow_left h1 (2 ^ d)
  rw [← pow_mul, ← hpow_eq, mul_pow, ← pow_mul, ← pow_mul, ← hpow_eq] at hpow1
  have hexp : (2 ^ κ₁ - 1) * (2 ^ d) ≤ 2 ^ κ₂ - 1 := by
    have hd1 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hk1 : 1 ≤ 2 ^ κ₁ := Nat.one_le_two_pow
    rw [Nat.sub_mul, one_mul, ← hpow_eq]
    omega
  have hlog_pow : (Nat.log2 L) ^ ((2 ^ κ₁ - 1) * (2 ^ d)) ≤ (Nat.log2 L) ^ (2 ^ κ₂ - 1) :=
    Nat.pow_le_pow_right hlog hexp
  exact le_trans hpow1 (Nat.mul_le_mul_left _ hlog_pow)

/-- **Deduction of `o(n log n)` (`intMulSubNLogN_46_implies_littleO`, 0 `sorry`):**
Any machine satisfying `IntMulSubNLogN 46` has `M.time L = o(L log₂ L)`, i.e. for every `K > 0`,
`K * M.time L ≤ L * Nat.log2 L` for all `L ≥ max N₀ (2 ^ ((C * K) ^ (2 ^ 46)))`. -/
theorem intMulSubNLogN_46_implies_littleO (h46 : IntMulSubNLogN 46) :
    Headline_TM2_LittleO_NLogN := by
  obtain ⟨M, hfin, C, N₀, hC, hT⟩ := h46
  refine ⟨M, hfin, fun K _ => ?_⟩
  set m := 2 ^ 46
  have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by decide)
  refine ⟨max N₀ (2 ^ ((C * K) ^ m)), fun L hL => ?_⟩
  have hL_N₀ : N₀ ≤ L := le_of_max_le_left hL
  have hL_pow : 2 ^ ((C * K) ^ m) ≤ L := le_of_max_le_right hL
  have hL_pos : L ≠ 0 := by
    have : 1 ≤ 2 ^ ((C * K) ^ m) := Nat.one_le_two_pow
    omega
  have hlog : (C * K) ^ m ≤ Nat.log2 L := (Nat.le_log2 hL_pos).2 hL_pow
  have h1 := hT L hL_N₀
  have hpow : (K * M.time L) ^ m ≤ (L * Nat.log2 L) ^ m := by
    calc (K * M.time L) ^ m
        = K ^ m * (M.time L) ^ m := mul_pow K (M.time L) m
      _ ≤ K ^ m * ((C * L) ^ m * (Nat.log2 L) ^ (m - 1)) := Nat.mul_le_mul_left (K ^ m) h1
      _ = (C * K) ^ m * (L ^ m * (Nat.log2 L) ^ (m - 1)) := by
          rw [mul_pow C L m, mul_pow C K m]
          ring
      _ ≤ (Nat.log2 L) * (L ^ m * (Nat.log2 L) ^ (m - 1)) :=
          Nat.mul_le_mul_right _ hlog
      _ = L ^ m * ((Nat.log2 L) ^ (m - 1) * Nat.log2 L) := by ring
      _ = L ^ m * (Nat.log2 L) ^ m := by rw [← pow_succ, hm1]
      _ = (L * Nat.log2 L) ^ m := (mul_pow L (Nat.log2 L) m).symm
  exact (Nat.pow_le_pow_iff_left (by decide : m ≠ 0)).1 hpow

end SubNLogN.S5
