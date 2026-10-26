import WP.W9sp.Raw

/-!
# WP.W9sp.Loop — counted loops with an amortised counter

* `callI_same'`: a test contract (stacks unchanged, result in the registers).
* `cdLoop`: `while ctr ≠ 0 do (dec ctr; body)`, a `W3_isZeroNat` test before every iteration.
  The body sees the counter values `n-1, …, 0`.
* `HT.cdLoop`: from the state family `St i` (counter `i`), the loop goes from `St n` to `St 0`; the
  body is only required for `i < n`. The decrement is charged at its exact contract cost
  `Cd·(zerosLead (i+1) + 1)`.
* `loopCost_amort`: with `W3_dec_amortised`, the counter work of the whole loop is `O(n)`.

Adapted from `WP.W9h.Loop` for `W9_splitPack`.
-/

namespace WP.W9sp

open TMFw TMFw.Contracts WP.W7k2

variable {a b : ℕ} {σ : Type}

/-- **Test call**: stacks unchanged, the register property `Q` holds afterwards. -/
theorem callI_same' {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) {Q : I.R → Prop} {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x)) (fun x => B (callMap dflt named x)) Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    Triple ρ (fun s => s.stk = B) (callI I named dflt l)
      (fun s => s.stk = B ∧ Q (l.get s.var)) T := by
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, hq⟩ := hs
  refine ⟨?_, hq⟩
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    exact ha x
  · push_neg at hg
    exact hb g hg

/-- `while ctr ≠ 0 do (dec ctr; body)`. -/
def cdLoop (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit) (lz : Lens σ Iz.R) (ld : Lens σ Id.R)
    (ctr dflt : Loc a b) (body : Prog (Loc a b) (fun _ => Sym) σ) :
    Prog (Loc a b) (fun _ => Sym) σ :=
  (callI Iz [ctr] dflt lz).seq
    (.loop (fun v => !(Iz.obs (lz.get v)))
      (((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz)))

theorem cdLoop_closed (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit) (lz : Lens σ Iz.R)
    (ld : Lens σ Id.R) (ctr dflt : Loc a b) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (hb : body.Closed) : (cdLoop Iz Id lz ld ctr dflt body).Closed :=
  ⟨callI_closed _ _ _ _, ⟨⟨callI_closed _ _ _ _, hb⟩, callI_closed _ _ _ _⟩⟩

/-- **Counted loop rule.** `St i` is the state with counter `i` (`natSyms i ++ rc`); for `i < n`
the body turns `St (i+1)` with the counter already decremented to `i` into `St i`. -/
theorem HT.cdLoop {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : Loc a b)
    (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc) (n : ℕ)
    (St : ℕ → Loc a b → List Sym) (hSt : ∀ i ≤ n, St i ctr = natSyms i ++ rc)
    (body : Prog (Loc a b) (fun _ => Sym) σ) (cb : ℕ → ℕ)
    (hbody : ∀ i < n, HT [] (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i)
      (cb i)) :
    HT [] (St n) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (zerosLead (Computability.encodeNat (i + 1)) + 1) + cb i + Cz)
        n) := by
  have htest : ∀ i ≤ n, Triple [] (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i hi =>
    callI_same' Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i hi)) []
  refine Triple.seq (htest n le_rfl) ?_
  have hloop := Triple.loop (ρ := []) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => k ≤ n ∧ s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (zerosLead (Computability.encodeNat (i + 1)) + 1) + cb i + Cz) ?_ ?_ ?_ n
  · exact Triple.conseq hloop (fun s hs => ⟨le_rfl, hs⟩) (fun s hs => hs.2.1) le_rfl
  · intro k
    by_cases hk : k + 1 ≤ n
    · have hdec : HT [] (St (k + 1)) (callI Id [ctr] dflt ld)
          (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
          (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
        HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
          (hd k rc _ hrc (hSt (k + 1) hk)) []
      have h1 := Triple.seq (Triple.seq hdec (hbody k (by omega))) (htest k (by omega))
      exact Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) le_rfl
    · intro s hs
      exact absurd hs.1 hk
  · intro k s hs
    show (!(Iz.obs (lz.get s.var))) = true
    rw [hs.2.2]
    simp
  · intro s hs
    show (!(Iz.obs (lz.get s.var))) = false
    rw [hs.2.2]
    simp

/-! ## Loop cost arithmetic -/

theorem loopCost_eq (B : ℕ → ℕ) : ∀ n, loopCost B n = ((List.range n).map (fun i => B i + 1)).sum + 1
  | 0 => rfl
  | n + 1 => by
    rw [loopCost, loopCost_eq B n, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem sum_succ_reflect (h : ℕ → ℕ) :
    ∀ n, ((List.range n).map (fun i => h (i + 1))).sum =
      ((List.range n).map (fun i => h (n - i))).sum
  | 0 => rfl
  | n + 1 => by
    have e1 : ((List.range (n + 1)).map (fun i => h (i + 1))).sum =
        ((List.range n).map (fun i => h (i + 1))).sum + h (n + 1) := by
      rw [List.range_succ, List.map_append, List.sum_append]
      simp
    have e2 : ((List.range (n + 1)).map (fun i => h (n + 1 - i))).sum =
        h (n + 1) + ((List.range n).map (fun i => h (n - i))).sum := by
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      have e3 : List.map ((fun i => h (n + 1 - i)) ∘ Nat.succ) (List.range n) =
          List.map (fun i => h (n - i)) (List.range n) := by
        apply List.map_congr_left
        intro i _
        simp only [Function.comp, Nat.succ_eq_add_one, Nat.add_sub_add_right]
      rw [e3, Nat.sub_zero]
    rw [e1, e2, sum_succ_reflect h n, Nat.add_comm]

theorem sum_map_split (Cd Cz c : ℕ) (f cb : ℕ → ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, cb i ≤ c) →
      (l.map (fun i => Cd * f i + cb i + Cz + 1)).sum ≤ Cd * (l.map f).sum + l.length * (c + Cz + 1)
  | [], _ => by simp
  | x :: l, h => by
    have h1 := sum_map_split Cd Cz c f cb l (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have h2 := h x (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [Nat.mul_add Cd (f x), Nat.succ_mul l.length (c + Cz + 1)]
    omega

/-- **Amortised loop cost**: `O(n)` counter work in total. -/
theorem loopCost_amort (ham : W3_dec_amortised) (Cd Cz c : ℕ) (cb : ℕ → ℕ) (n : ℕ)
    (hcb : ∀ i < n, cb i ≤ c) :
    loopCost (fun i => Cd * (zerosLead (Computability.encodeNat (i + 1)) + 1) + cb i + Cz) n ≤
      Cd * (2 * n + bitLen n) + n * (c + Cz + 1) + 1 := by
  rw [loopCost_eq]
  have h1 : ((List.range n).map (fun i => zerosLead (Computability.encodeNat (i + 1)) + 1)).sum ≤
      2 * n + bitLen n := by
    rw [sum_succ_reflect (fun j => zerosLead (Computability.encodeNat j) + 1) n]
    exact ham n n le_rfl
  have h2 := sum_map_split Cd Cz c (fun i => zerosLead (Computability.encodeNat (i + 1)) + 1) cb
    (List.range n) (fun i hi => hcb i (List.mem_range.mp hi))
  rw [List.length_range] at h2
  have h3 : Cd * ((List.range n).map (fun i => zerosLead (Computability.encodeNat (i + 1)) + 1)).sum
      ≤ Cd * (2 * n + bitLen n) := Nat.mul_le_mul_left _ h1
  beta_reduce at h2 h3 ⊢
  omega

#assert_std_axioms callI_same' cdLoop_closed HT.cdLoop loopCost_eq sum_succ_reflect sum_map_split
  loopCost_amort

end WP.W9sp
