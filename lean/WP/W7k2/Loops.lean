import WP.W7k2.Ops

/-!
# WP.W7k2.Loops — counted loops and reversed list emission

* `callI_same`: a test contract (stacks unchanged, result in the registers).
* `cdLoop`: `while ctr ≠ 0 do (dec ctr; body)` with a `W3_isZeroNat` test before every iteration;
  the body sees the counter values `n-1, n-2, …, 0`, so it emits list entries **in reverse order**.
  `HT.cdLoop`: from the state family `St i` (counter `i`), the loop goes from `St n` to `St 0`.
* `sfx f i n`: the suffix `f i ++ f (i+1) ++ … ++ f (n-1)`; `sfx_zero` connects it to
  `((List.range n).map f).flatten`, the shape of every table segment in `Contracts/W7/Format.lean`.
  Emitting entries `n-1, …, 0` onto a stack builds `sfx f 0 n` with its first symbol on top.
-/

namespace WP.W7k2

open TMFw TMFw.Contracts

/-- Body of `W3_isZeroNat`. -/
def SpecIsZero (I : Inst 1 4 Bool) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms a ++ rx → Runs I.P S S (fun r => I.obs r = decide (a = 0)) C

/-- Body of `W3_decNat`. -/
def SpecDec (I : Inst 1 4 Unit) (C : ℕ) : Prop :=
  ∀ (a : ℕ) (rx : List Sym) (S : Loc 1 I.m → List Sym), TermOK rx →
    S (.inl 0) = natSyms (a + 1) ++ rx →
    Runs I.P S (Function.update S (.inl 0) (natSyms a ++ rx)) (fun _ => True)
      (C * (zerosLead (Computability.encodeNat (a + 1)) + 1))

variable {a b : ℕ} {σ : Type}

/-- **Test call**: stacks unchanged, the register property `Q` holds afterwards. -/
theorem callI_same {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
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

/-- **Counted loop rule.** `St i` is the state with counter `i` (`natSyms i ++ rc`); the body
turns `St (i+1)` with the counter already decremented to `i` into `St i`. -/
theorem HT.cdLoop {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : Loc a b)
    (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc) (St : ℕ → Loc a b → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : Prog (Loc a b) (fun _ => Sym) σ)
    (cb : ℕ → ℕ) (ρ : List (Prog (Loc a b) (fun _ => Sym) σ))
    (hbody : ∀ i, HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    ∀ n, HT ρ (St n) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) n) := by
  intro n
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i)) ρ
  refine Triple.seq (htest n) ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun k s => s.stk = St k ∧ Iz.obs (lz.get s.var) = decide (k = 0))
    (B := fun i => Cd * (bitLen (i + 1) + 1) + cb i + Cz) ?_ ?_ ?_ n
  · exact Triple.post hloop (fun s hs => hs.1)
  · intro k
    have hdec : HT ρ (St (k + 1)) (callI Id [ctr] dflt ld)
        (Function.update (St (k + 1)) ctr (natSyms k ++ rc))
        (Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1)) :=
      HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (k + 1)) (.inl 0) _
        (hd k rc _ hrc (hSt (k + 1))) ρ
    have hzl : zerosLead (Computability.encodeNat (k + 1)) ≤ bitLen (k + 1) :=
      zerosLead_le_length _
    have h1 := Triple.seq (Triple.seq hdec (hbody k)) (htest k)
    refine Triple.conseq h1 (fun s hs => hs.1) (fun s hs => hs) ?_
    have : Cd * (zerosLead (Computability.encodeNat (k + 1)) + 1) ≤ Cd * (bitLen (k + 1) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    show _ ≤ Cd * (bitLen (k + 1) + 1) + cb k + Cz
    omega
  · intro k s hs
    simp [hs.2]
  · intro s hs
    simp [hs.2]

/-! ## Suffixes of flattened maps (reversed emission) -/

/-- `f i ++ f (i+1) ++ … ++ f (n-1)`. -/
def sfx (f : ℕ → List Sym) (i n : ℕ) : List Sym := ((List.range' i (n - i)).map f).flatten

theorem sfx_zero (f : ℕ → List Sym) (n : ℕ) : sfx f 0 n = ((List.range n).map f).flatten := by
  simp [sfx, List.range_eq_range']

theorem sfx_self (f : ℕ → List Sym) (n : ℕ) : sfx f n n = [] := by
  simp [sfx]

theorem sfx_succ (f : ℕ → List Sym) {i n : ℕ} (h : i < n) : sfx f i n = f i ++ sfx f (i + 1) n := by
  unfold sfx
  obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
  rw [hk, List.range'_succ, show n - (i + 1) = k by omega]
  simp

theorem sfx_congr {f g : ℕ → List Sym} {i n : ℕ} (h : ∀ j, i ≤ j → j < n → f j = g j) :
    sfx f i n = sfx g i n := by
  unfold sfx
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range'] at hj
  exact h j (by omega) (by omega)

#assert_std_axioms callI_same cdLoop_closed HT.cdLoop sfx_zero sfx_self sfx_succ sfx_congr

end WP.W7k2
