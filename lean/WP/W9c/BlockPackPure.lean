import WP.W9c.Iface
import WP.W7k2.Arith

/-!
# WP.W9c.BlockPackPure — pure facts behind `W9c_blockPack`

* `qMag p_in q v`: the magnitude the machine computes for `gQuantizeCoordToScale p_in q v`
  (`gQuant_eq`). With `u = p_in + 1`: shift `|v|` left by `q - u` (if `u < q`), or right by
  `u - q` after a decrement when `v < 0`; then `(· + 1) / 2`.
* `aP` / `aN`: the parts routed to the positive / negative unsigned carry chain
  (`aP_sub_aN`: their difference is the quantized value).
* `chain k as`: the carry chain at radix `2^k` (chunks LSB first, final carry), and `hval`, the
  value the Horner pass rebuilds from them (`hval_chain`).
* `packNat` and `pack_sub`: the two unsigned packs differ by the signed pack.
* bounds used by the cost proof.
-/

namespace WP.W9c.BlockPack

open TMFw TMFw.Contracts IntMul WP.W7k2

/-! ## Quantization -/

/-- Magnitude of the quantized value, as the machine computes it. -/
def qMag (p_in q : ℕ) (v : ℤ) : ℕ :=
  ((if p_in + 1 < q then v.natAbs * 2 ^ (q - (p_in + 1))
    else (if v < 0 then v.natAbs - 1 else v.natAbs) / 2 ^ (p_in + 1 - q)) + 1) / 2

theorem nat_round_half (a e : ℕ) : (a + 2 ^ e) / 2 ^ (e + 1) = (a / 2 ^ e + 1) / 2 := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.add_div_right _ (by positivity)]

theorem int_floor_neg (N D : ℕ) (hD : 0 < D) :
    ((D : ℤ) - 1 - (N : ℤ)) / (D : ℤ) = -((N / D : ℕ) : ℤ) := by
  have h1 := Int.mul_ediv_add_emod (N : ℤ) (D : ℤ)
  have h2 : 0 ≤ (N : ℤ) % (D : ℤ) := Int.emod_nonneg _ (by omega)
  have h3 : (N : ℤ) % (D : ℤ) < (D : ℤ) := Int.emod_lt_of_pos _ (by omega)
  have h4 : ((N / D : ℕ) : ℤ) = (N : ℤ) / (D : ℤ) := by push_cast; rfl
  rw [h4]
  have key := (Int.ediv_emod_unique (a := (D : ℤ) - 1 - (N : ℤ)) (b := (D : ℤ))
    (r := (D : ℤ) - 1 - (N : ℤ) % (D : ℤ)) (q := -((N : ℤ) / (D : ℤ))) (by omega)).mpr
    ⟨by linear_combination (-1 : ℤ) * h1, by omega, by omega⟩
  exact key.1

/-- **The machine quantization equals the snapshot's** `gQuantizeCoordToScale`. -/
theorem gQuant_eq (p_in q : ℕ) (v : ℤ) :
    gQuantizeCoordToScale p_in q v =
      if v < 0 then -((qMag p_in q v : ℕ) : ℤ) else ((qMag p_in q v : ℕ) : ℤ) := by
  rw [IntMulTM.Contracts.W8_gQuantizeCoordToScale_shift_holds]
  unfold qMag
  by_cases hL : p_in + 2 ≤ q
  · rw [if_pos hL, if_pos (by omega : p_in + 1 < q)]
    obtain ⟨s, hs⟩ : ∃ s, q - (p_in + 2) = s := ⟨_, rfl⟩
    have hs1 : q - (p_in + 1) = s + 1 := by omega
    rw [hs, hs1, pow_succ, ← mul_assoc]
    have e : (v.natAbs * 2 ^ s * 2 + 1) / 2 = v.natAbs * 2 ^ s := by omega
    rw [e]
    by_cases hv : v < 0
    · rw [if_pos hv]
      have hva : (v.natAbs : ℤ) = -v := by omega
      rw [Nat.cast_mul, hva]
      ring
    · rw [if_neg hv]
      have hva : (v.natAbs : ℤ) = v := by omega
      rw [Nat.cast_mul, hva]
  · rw [if_neg hL, if_neg (by omega : ¬ p_in + 1 < q)]
    obtain ⟨e, he⟩ : ∃ e, p_in + 1 - q = e := ⟨_, rfl⟩
    have he2 : p_in + 2 - q = e + 1 := by omega
    rw [he, he2]
    unfold divRoundPow2
    rw [if_neg (by omega), Nat.add_sub_cancel]
    by_cases hv : v < 0
    · rw [if_pos hv, if_pos hv]
      have ha : 1 ≤ v.natAbs := by omega
      have hva : (v.natAbs : ℤ) = -v := by omega
      have key : v + ((2 ^ e : ℕ) : ℤ) =
          ((2 ^ (e + 1) : ℕ) : ℤ) - 1 - ((v.natAbs - 1 + 2 ^ e : ℕ) : ℤ) := by
        rw [Nat.cast_add, Nat.cast_sub ha, hva, pow_succ]
        push_cast
        ring
      rw [key, int_floor_neg _ _ (by positivity), nat_round_half]
    · rw [if_neg hv, if_neg hv]
      obtain ⟨a, rfl⟩ : ∃ a : ℕ, v = (a : ℤ) := ⟨v.toNat, by omega⟩
      rw [Int.natAbs_natCast, ← nat_round_half]
      push_cast
      rfl

/-- Positive part (routed to the positive chain). -/
def aP (p_in q : ℕ) (v : ℤ) : ℕ := if v < 0 then 0 else qMag p_in q v

/-- Negative part (routed to the negative chain). -/
def aN (p_in q : ℕ) (v : ℤ) : ℕ := if v < 0 then qMag p_in q v else 0

theorem aP_sub_aN (p_in q : ℕ) (v : ℤ) :
    ((aP p_in q v : ℕ) : ℤ) - ((aN p_in q v : ℕ) : ℤ) = gQuantizeCoordToScale p_in q v := by
  rw [gQuant_eq]
  unfold aP aN
  split_ifs <;> simp

/-! ## Packs and the carry chain -/

/-- Unsigned Kronecker evaluation `Σ aᵢ Mⁱ`. -/
def packNat (M : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: as => a + M * packNat M as

theorem packNat_append (M : ℕ) : ∀ (l l' : List ℕ),
    packNat M (l ++ l') = packNat M l + M ^ l.length * packNat M l'
  | [], l' => by simp [packNat]
  | a :: l, l' => by
    simp only [List.cons_append, packNat, packNat_append M l l', List.length_cons, pow_succ]
    ring

/-- The two unsigned packs differ by the signed pack. -/
theorem pack_sub (M : ℕ) {α : Type} (f g : α → ℕ) : ∀ l : List α,
    ((packNat M (l.map f) : ℕ) : ℤ) - ((packNat M (l.map g) : ℕ) : ℤ) =
      packSignedKronecker (M : ℤ) (l.map fun x => (f x : ℤ) - (g x : ℤ))
  | [] => by simp [packNat, packSignedKronecker]
  | x :: l => by
    simp only [List.map_cons, packNat, packSignedKronecker]
    rw [← pack_sub M f g l]
    push_cast
    ring

/-- One carry step at radix `2^k`: chunk `(c + a) % 2^k` appended, carry `(c + a) / 2^k`. -/
def chainStep (k : ℕ) (st : List ℕ × ℕ) (a : ℕ) : List ℕ × ℕ :=
  (st.1 ++ [(st.2 + a) % 2 ^ k], (st.2 + a) / 2 ^ k)

/-- The carry chain over the addends `as`, from carry `0`. -/
def chain (k : ℕ) (as : List ℕ) : List ℕ × ℕ := as.foldl (chainStep k) ([], 0)

theorem chain_nil (k : ℕ) : chain k [] = ([], 0) := rfl

theorem chain_snoc (k : ℕ) (l : List ℕ) (a : ℕ) :
    chain k (l ++ [a]) = chainStep k (chain k l) a := by
  simp [chain, List.foldl_append]

/-- Value of chunks `cs` (LSB first) under a top carry `c`. -/
def hval (M : ℕ) (cs : List ℕ) (c : ℕ) : ℕ := packNat M cs + M ^ cs.length * c

theorem hval_nil (M c : ℕ) : hval M [] c = c := by simp [hval, packNat]

theorem hval_cons (M x : ℕ) (cs : List ℕ) (c : ℕ) : hval M (x :: cs) c = x + M * hval M cs c := by
  simp only [hval, packNat, List.length_cons, pow_succ]
  ring

theorem hval_chainStep (k : ℕ) (st : List ℕ × ℕ) (a : ℕ) :
    hval (2 ^ k) (chainStep k st a).1 (chainStep k st a).2 =
      hval (2 ^ k) st.1 st.2 + (2 ^ k) ^ st.1.length * a := by
  unfold hval chainStep
  simp only [packNat_append, packNat, List.length_append, List.length_singleton, pow_succ]
  have h := Nat.mod_add_div (st.2 + a) (2 ^ k)
  calc _ = packNat (2 ^ k) st.1 + (2 ^ k) ^ st.1.length *
        ((st.2 + a) % 2 ^ k + 2 ^ k * ((st.2 + a) / 2 ^ k)) := by ring
    _ = _ := by rw [h]; ring

theorem hval_foldl (k : ℕ) : ∀ (as : List ℕ) (st : List ℕ × ℕ),
    hval (2 ^ k) (as.foldl (chainStep k) st).1 (as.foldl (chainStep k) st).2 =
      hval (2 ^ k) st.1 st.2 + (2 ^ k) ^ st.1.length * packNat (2 ^ k) as ∧
    (as.foldl (chainStep k) st).1.length = st.1.length + as.length
  | [], st => by simp [packNat]
  | a :: as, st => by
    obtain ⟨h1, h2⟩ := hval_foldl k as (chainStep k st a)
    have hl : (chainStep k st a).1.length = st.1.length + 1 := by simp [chainStep]
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons]
      rw [h1, hval_chainStep, hl, packNat, pow_succ]
      ring
    · simp only [List.foldl_cons, List.length_cons]
      rw [h2, hl]
      ring

/-- **The Horner value of the chain is the unsigned pack.** -/
theorem hval_chain (k : ℕ) (as : List ℕ) :
    hval (2 ^ k) (chain k as).1 (chain k as).2 = packNat (2 ^ k) as := by
  have h := (hval_foldl k as ([], 0)).1
  simpa [chain, hval_nil] using h

theorem length_chain (k : ℕ) (as : List ℕ) : (chain k as).1.length = as.length := by
  have h := (hval_foldl k as ([], 0)).2
  simpa [chain] using h

theorem chunk_lt_foldl (k : ℕ) : ∀ (as : List ℕ) (st : List ℕ × ℕ), (∀ x ∈ st.1, x < 2 ^ k) →
    ∀ x ∈ (as.foldl (chainStep k) st).1, x < 2 ^ k
  | [], st, h => h
  | a :: as, st, h => by
    refine chunk_lt_foldl k as (chainStep k st a) (fun x hx => ?_)
    simp only [chainStep, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · exact Nat.mod_lt _ (by positivity)

theorem chunk_lt (k : ℕ) (as : List ℕ) : ∀ x ∈ (chain k as).1, x < 2 ^ k :=
  chunk_lt_foldl k as ([], 0) (fun _ hx => absurd hx (by simp))

theorem carry_lt_foldl (k A : ℕ) (hk : 1 ≤ k) : ∀ (as : List ℕ) (st : List ℕ × ℕ),
    (∀ x ∈ as, x < 2 ^ A) → st.2 < 2 ^ A → (as.foldl (chainStep k) st).2 < 2 ^ A
  | [], _, _, h => h
  | a :: as, st, has, h => by
    refine carry_lt_foldl k A hk as (chainStep k st a) (fun x hx => has x (by simp [hx])) ?_
    have ha := has a (by simp)
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h3 : (st.2 + a) / 2 ^ k ≤ (st.2 + a) / 2 := Nat.div_le_div_left h2 (by norm_num)
    show (st.2 + a) / 2 ^ k < 2 ^ A
    omega

theorem carry_lt (k A : ℕ) (hk : 1 ≤ k) (as : List ℕ) (has : ∀ x ∈ as, x < 2 ^ A) :
    (chain k as).2 < 2 ^ A :=
  carry_lt_foldl k A hk as ([], 0) has (by positivity)

/-- Size of an unsigned pack. -/
theorem packNat_lt (k A : ℕ) (hk : 1 ≤ k) : ∀ l : List ℕ, (∀ x ∈ l, x < 2 ^ A) →
    packNat (2 ^ k) l < 2 ^ (l.length * (k + A))
  | [], _ => by simp [packNat]
  | x :: l, h => by
    have ih := packNat_lt k A hk l (fun y hy => h y (by simp [hy]))
    have hx := h x (by simp)
    simp only [packNat, List.length_cons]
    have e : 2 ^ ((l.length + 1) * (k + A)) = 2 ^ A * 2 ^ k * 2 ^ (l.length * (k + A)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring
    rw [e]
    set p := packNat (2 ^ k) l
    set c := 2 ^ (l.length * (k + A))
    have ha : 1 ≤ 2 ^ A := Nat.one_le_two_pow
    have hb : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have s1 : x + 2 ^ k * p < 2 ^ A + 2 ^ k * p := by omega
    have s2 : 2 ^ A ≤ 2 ^ A * 2 ^ k := Nat.le_mul_of_pos_right _ (by omega)
    have s3 : 2 ^ k * p ≤ 2 ^ A * 2 ^ k * p := by
      rw [mul_assoc]
      exact Nat.le_mul_of_pos_left _ (by omega)
    have s4 : 2 ^ A * 2 ^ k * (p + 1) ≤ 2 ^ A * 2 ^ k * c := Nat.mul_le_mul_left _ (by omega)
    have s5 : 2 ^ A * 2 ^ k * (p + 1) = 2 ^ A * 2 ^ k * p + 2 ^ A * 2 ^ k := by ring
    omega

/-- Bound on the quantized magnitude. -/
theorem qMag_lt (p_in q B : ℕ) (v : ℤ) (hv : v.natAbs < 2 ^ B) : qMag p_in q v < 2 ^ (B + q) := by
  unfold qMag
  have hB : 2 ^ B ≤ 2 ^ (B + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
  split_ifs with h1 h2
  · have : v.natAbs * 2 ^ (q - (p_in + 1)) < 2 ^ (B + q) := by
      calc v.natAbs * 2 ^ (q - (p_in + 1)) < 2 ^ B * 2 ^ (q - (p_in + 1)) :=
            Nat.mul_lt_mul_of_pos_right hv (by positivity)
        _ = 2 ^ (B + (q - (p_in + 1))) := by rw [pow_add]
        _ ≤ 2 ^ (B + q) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : (v.natAbs - 1) / 2 ^ (p_in + 1 - q) ≤ v.natAbs - 1 := Nat.div_le_self _ _
    omega
  · have : v.natAbs / 2 ^ (p_in + 1 - q) ≤ v.natAbs := Nat.div_le_self _ _
    omega

theorem aP_le (p_in q : ℕ) (v : ℤ) : aP p_in q v ≤ qMag p_in q v := by
  unfold aP; split_ifs <;> omega

theorem aN_le (p_in q : ℕ) (v : ℤ) : aN p_in q v ≤ qMag p_in q v := by
  unfold aN; split_ifs <;> omega

/-! ## Symbol lists -/

theorem listSyms_nil : listSyms [] = [] := rfl

theorem listSyms_cons (v : ℤ) (vs : List ℤ) :
    listSyms (v :: vs) = intSyms v ++ Sym.sep :: listSyms vs := by
  simp [listSyms, List.flatMap_cons]

/-- Chunks on a chunk stack, each followed by `sep`, first on top. -/
def chunkSyms (l : List ℕ) : List Sym := l.flatMap fun c => natSyms c ++ [Sym.sep]

theorem chunkSyms_nil : chunkSyms [] = [] := rfl

theorem chunkSyms_cons (x : ℕ) (l : List ℕ) :
    chunkSyms (x :: l) = natSyms x ++ Sym.sep :: chunkSyms l := by
  simp [chunkSyms, List.flatMap_cons]

theorem chunkSyms_snoc_rev (l : List ℕ) (x : ℕ) :
    chunkSyms (l ++ [x]).reverse = natSyms x ++ Sym.sep :: chunkSyms l.reverse := by
  rw [List.reverse_append, List.reverse_singleton, List.singleton_append, chunkSyms_cons]

#assert_std_axioms nat_round_half int_floor_neg gQuant_eq aP_sub_aN packNat_append pack_sub
  chain_snoc hval_nil hval_cons hval_chainStep hval_foldl hval_chain length_chain chunk_lt
  carry_lt packNat_lt qMag_lt aP_le aN_le listSyms_cons chunkSyms_cons chunkSyms_snoc_rev

end WP.W9c.BlockPack
