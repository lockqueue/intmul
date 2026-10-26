import Contracts.Machine.W4
import WP.W4o.RouteDefs

/-!
# WP.W4o.RouteMath — the router's recursion computes `oddRouteL` (pure)

`rt W n B v` is the recursion of W4o's data-driven router. The even outputs come from the
input parity `B.head` with offset block `B.tail`. The odd outputs come from the other parity with
offset block `(B + W mod 2^n).tail`.

* `rt_eq_oddRouteL`: for odd `w`, `|B| = n` and `|v| = 2^n`,
  `rt (encodeNat w) n B v = oddRouteL n w (bitsVal B) v`.
* `length_sel`, `mem_sel`, `length_rt`, `mem_rt`, `flatten_length_rt`: the size and membership
  facts the machine proof needs.

The proof of the main theorem goes index by index (`getD`):
* output `2u` is entry `(w·u + b') mod 2^n` of `sel β v`, i.e. entry
  `2·((w·u + b') mod 2^n) + β = (w·2u + b) mod 2^(n+1)` of `v`;
* output `2u+1` is entry `(w·u + c/2) mod 2^n` of `sel (!β) v`, with `c = (b + w) mod 2^(n+1)`
  (`bitsVal_addT_add`) and `c mod 2 = 1 − β` (`w` odd).

Here `B = β :: B'`, `b' = bitsVal B'`, `b = 2b' + β`.
Helper lemmas live in the sub-namespace `TMFw.W4o.RouteMath`.
-/

namespace TMFw.W4o

open TMFw TMFw.Contracts Computability

/-! The definitions `sel`, `inter`, `rt` are in `WP.W4o.RouteDefs`. -/

/-! ## Helpers (namespace `TMFw.W4o.RouteMath`) -/

namespace RouteMath

section Lists

variable {α : Type}

theorem length_sel_false_true : ∀ v : List α,
    (sel false v).length = (v.length + 1) / 2 ∧ (sel true v).length = v.length / 2
  | [] => by simp [sel]
  | a :: l => by
    obtain ⟨h1, h2⟩ := length_sel_false_true l
    refine ⟨?_, ?_⟩
    · show (sel true l).length + 1 = (l.length + 1 + 1) / 2
      omega
    · show (sel false l).length = (l.length + 1) / 2
      exact h1

theorem length_inter : ∀ l m : List α, (inter l m).length = l.length + m.length
  | a :: l, b :: m => by
    show (inter l m).length + 1 + 1 = (l.length + 1) + (m.length + 1)
    rw [length_inter l m]
    omega
  | [], m => by
    show m.length = 0 + m.length
    omega
  | a :: l, [] => rfl

theorem mem_inter : ∀ (l m : List α) (x : α), x ∈ inter l m → x ∈ l ∨ x ∈ m
  | a :: l, b :: m, x, h => by
    have h' : x = a ∨ x = b ∨ x ∈ inter l m := by simpa [inter] using h
    rcases h' with rfl | rfl | h'
    · exact Or.inl (by simp)
    · exact Or.inr (by simp)
    · rcases mem_inter l m x h' with h'' | h''
      · exact Or.inl (List.mem_cons_of_mem _ h'')
      · exact Or.inr (List.mem_cons_of_mem _ h'')
  | [], _, _, h => Or.inr h
  | _ :: _, [], _, h => Or.inl h

theorem getD_sel : ∀ (v : List α) (β : Bool) (i : ℕ) (d : α),
    (sel β v).getD i d = v.getD (2 * i + β.toNat) d
  | [], β, i, d => by cases β <;> simp [sel]
  | a :: l, false, 0, d => rfl
  | a :: l, false, i + 1, d => by
    show (sel true l).getD i d = (a :: l).getD (2 * (i + 1) + 0) d
    rw [getD_sel l true i d, Bool.toNat_true, show 2 * (i + 1) + 0 = (2 * i + 1) + 1 by omega,
      List.getD_cons_succ]
  | a :: l, true, i, d => by
    show (sel false l).getD i d = (a :: l).getD (2 * i + 1) d
    rw [getD_sel l false i d, Bool.toNat_false, Nat.add_zero, List.getD_cons_succ]

theorem getD_inter : ∀ (l m : List α), l.length = m.length → ∀ (i : ℕ) (d : α),
    (inter l m).getD (2 * i) d = l.getD i d ∧ (inter l m).getD (2 * i + 1) d = m.getD i d
  | [], [], _, i, d => by simp [inter]
  | a :: l, b :: m, _, 0, d => ⟨rfl, rfl⟩
  | a :: l, b :: m, h, i + 1, d => by
    have ih := getD_inter l m (by simpa using h) i d
    refine ⟨?_, ?_⟩
    · show (a :: b :: inter l m).getD (2 * (i + 1)) d = (a :: l).getD (i + 1) d
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
      simp only [List.getD_cons_succ]
      exact ih.1
    · show (a :: b :: inter l m).getD (2 * (i + 1) + 1) d = (b :: m).getD (i + 1) d
      rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega]
      simp only [List.getD_cons_succ]
      exact ih.2
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

/-- Lists of equal length with equal entries (below the length) are equal. -/
theorem ext_getD' (d : α) : ∀ (l₁ l₂ : List α), l₁.length = l₂.length →
    (∀ i, i < l₁.length → l₁.getD i d = l₂.getD i d) → l₁ = l₂
  | [], [], _, _ => rfl
  | a :: l₁, b :: l₂, hl, h => by
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    rw [h0, ext_getD' d l₁ l₂ (by simpa using hl)
      (fun i hi => by simpa using h (i + 1) (by simp only [List.length_cons]; omega))]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

end Lists

section Flatten

variable {β : Type}

theorem flatten_length_inter : ∀ l m : List (List β),
    (inter l m).flatten.length = l.flatten.length + m.flatten.length
  | a :: l, b :: m => by
    show (a ++ (b ++ (inter l m).flatten)).length =
      (a ++ l.flatten).length + (b ++ m.flatten).length
    simp only [List.length_append, flatten_length_inter l m]
    omega
  | [], m => by
    show m.flatten.length = 0 + m.flatten.length
    omega
  | a :: l, [] => by
    show (a :: l).flatten.length = (a :: l).flatten.length + 0
    rfl

theorem flatten_length_sel : ∀ v : List (List β),
    (sel false v).flatten.length + (sel true v).flatten.length = v.flatten.length
  | [] => rfl
  | a :: l => by
    have ih := flatten_length_sel l
    show (a ++ (sel true l).flatten).length + (sel false l).flatten.length = (a ++ l.flatten).length
    rw [List.length_append, List.length_append]
    omega

end Flatten

section Route

variable {α : Type} [Inhabited α]

theorem length_oddRouteL (k w b : ℕ) (v : List α) : (oddRouteL k w b v).length = 2 ^ k := by
  simp [oddRouteL]

theorem getD_oddRouteL (k w b : ℕ) (v : List α) (u : ℕ) (hu : u < 2 ^ k) (d : α) :
    (oddRouteL k w b v).getD u d = v.getD ((w * u + b) % 2 ^ k) default := by
  unfold oddRouteL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]
  rfl

end Route

end RouteMath

open RouteMath

/-! ## Sizes and membership -/

theorem length_sel {α : Type} (n : ℕ) (β : Bool) (v : List α) (hv : v.length = 2 ^ (n + 1)) :
    (sel β v).length = 2 ^ n := by
  obtain ⟨h1, h2⟩ := length_sel_false_true v
  have hp : 2 ^ (n + 1) = 2 * 2 ^ n := Nat.pow_succ'
  cases β
  · rw [h1, hv, hp]
    omega
  · rw [h2, hv, hp]
    omega

theorem mem_sel {α : Type} (β : Bool) (v : List α) (x : α) (h : x ∈ sel β v) : x ∈ v := by
  induction v generalizing β with
  | nil => cases β <;> simp [sel] at h
  | cons a l ih =>
    cases β
    · have h' : x = a ∨ x ∈ sel true l := by simpa [sel] using h
      rcases h' with rfl | h'
      · simp
      · exact List.mem_cons_of_mem a (ih true h')
    · exact List.mem_cons_of_mem a (ih false h)

theorem length_rt {α : Type} (W : List Bool) :
    ∀ (n : ℕ) (B : List Bool) (v : List α), v.length = 2 ^ n → (rt W n B v).length = 2 ^ n
  | 0, _, _, hv => hv
  | n + 1, B, v, hv => by
    show (inter (rt W n B.tail (sel (B.headD false) v))
      (rt W n (addT false B W false).tail (sel (!B.headD false) v))).length = 2 ^ (n + 1)
    rw [length_inter, length_rt W n _ _ (length_sel n _ v hv),
      length_rt W n _ _ (length_sel n _ v hv), Nat.pow_succ']
    omega

theorem mem_rt {α : Type} (W : List Bool) :
    ∀ (n : ℕ) (B : List Bool) (v : List α) (x : α), x ∈ rt W n B v → x ∈ v
  | 0, _, _, _, h => h
  | n + 1, B, v, x, h => by
    rcases mem_inter _ _ x h with h' | h'
    · exact mem_sel _ v x (mem_rt W n _ _ x h')
    · exact mem_sel _ v x (mem_rt W n _ _ x h')

/-- total size is preserved (no length hypothesis needed: `inter`/`sel` are permutations) -/
theorem flatten_length_rt {β : Type} (W : List Bool) :
    ∀ (n : ℕ) (B : List Bool) (v : List (List β)),
      (rt W n B v).flatten.length = v.flatten.length
  | 0, _, _ => rfl
  | n + 1, B, v => by
    show (inter (rt W n B.tail (sel (B.headD false) v))
      (rt W n (addT false B W false).tail (sel (!B.headD false) v))).flatten.length =
        v.flatten.length
    rw [flatten_length_inter, flatten_length_rt W n, flatten_length_rt W n]
    have h := flatten_length_sel v
    generalize B.headD false = b
    cases b
    · exact h
    · show (sel true v).flatten.length + (sel false v).flatten.length = v.flatten.length
      omega

/-! ## The recursion computes `oddRouteL` -/

/-- **Main**: the recursion computes the contract's pure spec. -/
theorem rt_eq_oddRouteL {α : Type} [Inhabited α] (w : ℕ) (hw : w % 2 = 1) :
    ∀ (n : ℕ) (B : List Bool) (v : List α), B.length = n → v.length = 2 ^ n →
      rt (encodeNat w) n B v = oddRouteL n w (bitsVal B) v
  | 0, B, v, hB, hv => by
    obtain ⟨a, rfl⟩ : ∃ a, v = [a] := List.length_eq_one_iff.mp (by simpa using hv)
    cases B with
    | nil => simp [rt, oddRouteL]
    | cons _ _ => simp at hB
  | n + 1, B, v, hB, hv => by
    cases B with
    | nil => simp at hB
    | cons β B' =>
      have hB' : B'.length = n := by simpa using hB
      have hp : 2 ^ (n + 1) = 2 * 2 ^ n := Nat.pow_succ'
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have hC : (addT false (β :: B') (encodeNat w) false).tail.length = n := by
        simp [length_addT, hB']
      have ih1 := rt_eq_oddRouteL w hw n B' (sel β v) hB' (length_sel n β v hv)
      have ih2 := rt_eq_oddRouteL w hw n _ (sel (!β) v) hC (length_sel n (!β) v hv)
      obtain ⟨c, hcdef⟩ : ∃ c, c = bitsVal (addT false (β :: B') (encodeNat w) false) :=
        ⟨_, rfl⟩
      have hct : bitsVal (addT false (β :: B') (encodeNat w) false).tail = c / 2 := by
        rw [bitsVal_tail, ← hcdef]
      have hc : c = (bitsVal B' + bitsVal B' + β.toNat + w) % 2 ^ (n + 1) := by
        rw [hcdef, bitsVal_addT_add, bitsVal_encodeNat, bitsVal_cons, Bool.toNat_false,
          Nat.add_zero, List.length_cons, hB']
      have hcpar : c % 2 = (!β).toNat := by
        have h2 : 2 ∣ 2 ^ (n + 1) := dvd_pow_self 2 (Nat.succ_ne_zero n)
        rw [hc, Nat.mod_mod_of_dvd _ h2]
        cases β <;> simp only [Bool.toNat_false, Bool.toNat_true, Bool.not_false,
          Bool.not_true] <;> omega
      have heven : ∀ u, (w * (2 * u) + (bitsVal B' + bitsVal B' + β.toNat)) % 2 ^ (n + 1) =
          2 * ((w * u + bitsVal B') % 2 ^ n) + β.toNat := by
        intro u
        rw [show w * (2 * u) + (bitsVal B' + bitsVal B' + β.toNat) =
          2 * (w * u + bitsVal B') + β.toNat by ring, hp]
        exact two_mul_add_mod _ _ _ (Bool.toNat_lt β) hpos
      have hodd : ∀ u, (w * (2 * u + 1) + (bitsVal B' + bitsVal B' + β.toNat)) % 2 ^ (n + 1) =
          2 * ((w * u + c / 2) % 2 ^ n) + (!β).toNat := by
        intro u
        have e1 : w * (2 * u + 1) + (bitsVal B' + bitsVal B' + β.toNat) =
            2 * (w * u) + (bitsVal B' + bitsVal B' + β.toNat + w) := by ring
        have e2 : (2 * (w * u) + (bitsVal B' + bitsVal B' + β.toNat + w)) % 2 ^ (n + 1) =
            (2 * (w * u) + c) % 2 ^ (n + 1) := by
          rw [hc, Nat.add_mod_mod]
        have e3 : 2 * (w * u) + c = 2 * (w * u + c / 2) + c % 2 := by omega
        rw [e1, e2, e3, hp, two_mul_add_mod _ _ _ (Nat.mod_lt _ (by norm_num)) hpos, hcpar]
      show inter (rt (encodeNat w) n B' (sel β v))
          (rt (encodeNat w) n (addT false (β :: B') (encodeNat w) false).tail (sel (!β) v)) =
        oddRouteL (n + 1) w (bitsVal (β :: B')) v
      rw [ih1, ih2, hct, bitsVal_cons]
      have hlen : (oddRouteL n w (bitsVal B') (sel β v)).length =
          (oddRouteL n w (c / 2) (sel (!β) v)).length := by
        rw [length_oddRouteL, length_oddRouteL]
      refine ext_getD' default _ _ ?_ ?_
      · rw [length_inter, length_oddRouteL, length_oddRouteL, length_oddRouteL, hp]
        omega
      · intro i hi
        rw [length_inter, length_oddRouteL, length_oddRouteL] at hi
        rcases Nat.even_or_odd' i with ⟨u, rfl | rfl⟩
        · have hu : u < 2 ^ n := by omega
          have hu2 : 2 * u < 2 ^ (n + 1) := by omega
          rw [(getD_inter _ _ hlen u default).1, getD_oddRouteL _ _ _ _ _ hu, getD_sel,
            getD_oddRouteL _ _ _ _ _ hu2, heven u]
        · have hu : u < 2 ^ n := by omega
          have hu2 : 2 * u + 1 < 2 ^ (n + 1) := by omega
          rw [(getD_inter _ _ hlen u default).2, getD_oddRouteL _ _ _ _ _ hu, getD_sel,
            getD_oddRouteL _ _ _ _ _ hu2, hodd u]

#assert_std_axioms RouteMath.length_sel_false_true RouteMath.length_inter RouteMath.mem_inter
  RouteMath.getD_sel RouteMath.getD_inter RouteMath.ext_getD' RouteMath.flatten_length_inter
  RouteMath.flatten_length_sel RouteMath.length_oddRouteL RouteMath.getD_oddRouteL

#assert_std_axioms length_sel mem_sel length_rt mem_rt flatten_length_rt rt_eq_oddRouteL

end TMFw.W4o
