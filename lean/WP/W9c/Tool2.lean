import WP.W9c.Tool

/-!
# WP.W9c.Tool2 — loop unfolding, counted loops (amortised), number moves

* `ht_whileTop_false` / `ht_whileTop_true`: one unfolding of `whileTop`, for loops whose
  invariant is indexed by a data list (structural induction instead of a counter).
* `cdLoop`: `while ctr ≠ 0 do (dec ctr; body)` with the **exact** decrement cost
  `zerosLead (encodeNat (i+1))` (`ht_cdLoop`), so `W3_dec_amortised` gives `O(n + |n|)`.
* `mvNum src dst tmp`: move `intSyms z ++ [sep]` keeping its orientation (`ht_mvNum`).
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2

variable {a b : ℕ} {σ : Type} {ρ : List (HP a b σ)}

/-! ## Inversion of evaluations -/

theorem eval_seq_inv {p q : HP a b σ} {s s' : St (Loc a b) (fun _ => Sym) σ} {t : ℕ}
    (h : Eval ρ (.seq p q) s s' t) :
    ∃ s1 t1 t2, Eval ρ p s s1 t1 ∧ Eval ρ q s1 s' t2 ∧ t = t1 + t2 := by
  cases h with
  | seq h1 h2 => exact ⟨_, _, _, h1, h2, rfl⟩

theorem eval_peek_inv {k : Loc a b} {f : σ → Option Sym → σ}
    {s s' : St (Loc a b) (fun _ => Sym) σ} {t : ℕ} (h : Eval ρ (.peek k f) s s' t) :
    s' = ⟨f s.var (s.stk k).head?, s.stk⟩ ∧ t = 1 := by
  cases h with
  | peek => exact ⟨rfl, rfl⟩

/-! ## Unfolding `whileTop` -/

theorem ht_whileTop_false (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (body : HP a b σ) (B : Loc a b → List Sym) (h : optT c (B k).head? = false) :
    HT ρ B (whileTop lS k c body) B 2 := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.peek ρ k (fun v o => lS.set v o) v S
  have e2 : Eval ρ (.loop (fun v => optT c (lS.get v)) (body.seq (peekS lS k)))
      ⟨lS.set v (S k).head?, S⟩ ⟨lS.set v (S k).head?, S⟩ 1 :=
    Eval.loop_false (by show optT c (lS.get (lS.set v (S k).head?)) = false; rw [lS.get_set]; exact h)
  exact ⟨_, 2, Eval.seq e1 e2, rfl, le_rfl⟩

theorem ht_whileTop_true (lS : Lens σ (Option Sym)) (k : Loc a b) (c : Sym → Bool)
    (body : HP a b σ) (B B' B'' : Loc a b → List Sym) {T₁ T₂ : ℕ}
    (h : optT c (B k).head? = true) (hb : HT ρ B body B' T₁)
    (hrest : HT ρ B' (whileTop lS k c body) B'' T₂) :
    HT ρ B (whileTop lS k c body) B'' (T₁ + T₂ + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  have e1 := Eval.peek ρ k (fun v o => lS.set v o) v S
  obtain ⟨⟨vb, Sb⟩, tb, eb, hSb, htb⟩ := hb ⟨lS.set v (S k).head?, S⟩ rfl
  change Sb = B' at hSb
  subst hSb
  have e3 := Eval.peek ρ k (fun v o => lS.set v o) vb Sb
  obtain ⟨s', t, er, hs', ht⟩ := hrest ⟨vb, Sb⟩ rfl
  obtain ⟨s1, t1, t2, ep, el, rfl⟩ := eval_seq_inv er
  obtain ⟨rfl, rfl⟩ := eval_peek_inv ep
  have e4 := Eval.loop_true (c := fun v => optT c (lS.get v))
    (by show optT c (lS.get (lS.set v (S k).head?)) = true; rw [lS.get_set]; exact h)
    (Eval.seq eb e3) el
  exact ⟨s', _, Eval.seq e1 e4, hs', by omega⟩

/-! ## Counted loops with the exact decrement cost -/

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

/-- A test call: stacks unchanged, register property afterwards. -/
theorem callI_same' {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) {Q : I.R → Prop} {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x)) (fun x => B (callMap dflt named x)) Q T) :
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
    (ctr dflt : Loc a b) (body : HP a b σ) : HP a b σ :=
  (callI Iz [ctr] dflt lz).seq
    (.loop (fun v => !(Iz.obs (lz.get v)))
      (((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz)))

theorem cdLoop_closed (Iz : Inst 1 4 Bool) (Id : Inst 1 4 Unit) (lz : Lens σ Iz.R)
    (ld : Lens σ Id.R) (ctr dflt : Loc a b) {body : HP a b σ} (hb : body.Closed) :
    (cdLoop Iz Id lz ld ctr dflt body).Closed :=
  ⟨callI_closed _ _ _ _, ⟨⟨callI_closed _ _ _ _, hb⟩, callI_closed _ _ _ _⟩⟩

/-- **Counted loop**, exact decrement cost. `St i`: counter `i` on `ctr`. -/
theorem ht_cdLoop {Iz : Inst 1 4 Bool} {Id : Inst 1 4 Unit} {Cz Cd : ℕ} (hz : SpecIsZero Iz Cz)
    (hd : SpecDec Id Cd) (lz : Lens σ Iz.R) (ld : Lens σ Id.R) (ctr dflt : Loc a b)
    (hcap : 4 + 1 ≤ a + b) (rc : List Sym) (hrc : TermOK rc) (St : ℕ → Loc a b → List Sym)
    (hSt : ∀ i, St i ctr = natSyms i ++ rc) (body : HP a b σ) (cb : ℕ → ℕ) (n : ℕ)
    (hbody : ∀ i < n, HT ρ (Function.update (St (i + 1)) ctr (natSyms i ++ rc)) body (St i) (cb i)) :
    HT ρ (St n) (cdLoop Iz Id lz ld ctr dflt body) (St 0)
      (Cz + loopCost (fun i => Cd * (zerosLead (Computability.encodeNat (i + 1)) + 1) + cb i + Cz)
        n) := by
  have htest : ∀ i, Triple ρ (fun s => s.stk = St i) (callI Iz [ctr] dflt lz)
      (fun s => s.stk = St i ∧ Iz.obs (lz.get s.var) = decide (i = 0)) Cz := fun i =>
    callI_same' Iz [ctr] dflt (List.nodup_singleton _) rfl hcap lz (St i)
      (hz i rc _ hrc (hSt i))
  refine Triple.seq (htest n) ?_
  have hloop := Triple.loop (ρ := ρ) (c := fun v => !(Iz.obs (lz.get v)))
    (p := ((callI Id [ctr] dflt ld).seq body).seq (callI Iz [ctr] dflt lz))
    (I := fun j s => j ≤ n ∧ s.stk = St j ∧ Iz.obs (lz.get s.var) = decide (j = 0))
    (B := fun i => Cd * (zerosLead (Computability.encodeNat (i + 1)) + 1) + cb i + Cz)
    (fun j => by
      by_cases hj : j < n
      · have hdec : HT ρ (St (j + 1)) (callI Id [ctr] dflt ld)
            (Function.update (St (j + 1)) ctr (natSyms j ++ rc))
            (Cd * (zerosLead (Computability.encodeNat (j + 1)) + 1)) :=
          HT.callI_upd Id [ctr] dflt (List.nodup_singleton _) rfl hcap ld (St (j + 1)) (.inl 0) _
            (hd j rc _ hrc (hSt (j + 1))) ρ
        have h1 := Triple.seq (Triple.seq hdec (hbody j hj)) (htest j)
        exact Triple.conseq h1 (fun s hs => hs.2.1) (fun s hs => ⟨by omega, hs⟩) le_rfl
      · intro s hs
        exact absurd hs.1 (by omega))
    (fun j s hs => by
      show (!(Iz.obs (lz.get s.var))) = true
      rw [hs.2.2]; simp)
    (fun s hs => by
      show (!(Iz.obs (lz.get s.var))) = false
      rw [hs.2.2]; simp) n
  exact Triple.conseq hloop (fun s hs => ⟨le_refl n, hs⟩) (fun s hs => hs.2.1) le_rfl

/-! ## Moving a number, keeping its orientation -/

/-- Symbols of a signed number: bits and signs. -/
def isNum : Sym → Bool
  | .bit _ => true
  | .pos => true
  | .neg => true
  | _ => false

theorem isNum_intSyms (z : ℤ) : ∀ y ∈ intSyms z, isNum y = true := by
  intro y hy
  simp only [intSyms, natSyms, List.mem_cons, List.mem_map] at hy
  rcases hy with rfl | ⟨b, -, rfl⟩
  · unfold sgnSym; split <;> rfl
  · rfl

theorem isNum_reverse_intSyms (z : ℤ) : ∀ y ∈ (intSyms z).reverse, isNum y = true :=
  fun y hy => isNum_intSyms z y (List.mem_reverse.mp hy)

/-- Move `intSyms z ++ [sep]` from `src` to `dst` (same orientation), via `tmp` (restored). -/
def mvNum (lS : Lens σ (Option Sym)) (src dst tmp : Loc a b) : HP a b σ :=
  (pushS tmp .mark).seq ((moveWhile lS isNum src tmp).seq ((mv1 lS src dst).seq
    ((moveWhile lS isNum tmp dst).seq (popS tmp))))

theorem mvNum_closed (lS : Lens σ (Option Sym)) (src dst tmp : Loc a b) :
    (mvNum lS src dst tmp).Closed :=
  ⟨trivial, moveWhile_closed _ _ _ _, mv1_closed _ _ _, moveWhile_closed _ _ _ _, trivial⟩

theorem ht_mvNum (lS : Lens σ (Option Sym)) {src dst tmp : Loc a b} (hsd : src ≠ dst)
    (hst : src ≠ tmp) (hdt : dst ≠ tmp) (B : Loc a b → List Sym) (z : ℤ) (rest : List Sym)
    (hB : B src = intSyms z ++ Sym.sep :: rest) :
    HT ρ B (mvNum lS src dst tmp)
      (Function.update (Function.update B src rest) dst (intSyms z ++ Sym.sep :: B dst))
      (8 * (intSyms z).length + 10) := by
  set B1 := Function.update B tmp (.mark :: B tmp) with hB1
  set B2 := Function.update (Function.update B1 src (Sym.sep :: rest)) tmp
    ((intSyms z).reverse ++ Sym.mark :: B tmp) with hB2
  set B3 := Function.update (Function.update B2 src rest) dst (Sym.sep :: B dst) with hB3
  set B4 := Function.update (Function.update B3 tmp (Sym.mark :: B tmp)) dst
    (intSyms z ++ Sym.sep :: B dst) with hB4
  have e1s : B1 src = intSyms z ++ Sym.sep :: rest := by rw [hB1, Function.update_of_ne hst]; exact hB
  have e1t : B1 tmp = Sym.mark :: B tmp := by rw [hB1, Function.update_self]
  have e2s : B2 src = Sym.sep :: rest := by
    rw [hB2, Function.update_of_ne hst, Function.update_self]
  have e2d : B2 dst = B dst := by
    rw [hB2, Function.update_of_ne hdt, Function.update_of_ne hsd.symm, hB1,
      Function.update_of_ne hdt]
  have e3t : B3 tmp = (intSyms z).reverse ++ Sym.mark :: B tmp := by
    rw [hB3, Function.update_of_ne hdt.symm, Function.update_of_ne hst.symm, hB2,
      Function.update_self]
  have e3d : B3 dst = Sym.sep :: B dst := by rw [hB3, Function.update_self]
  have e4t : B4 tmp = Sym.mark :: B tmp := by
    rw [hB4, Function.update_of_ne hdt.symm, Function.update_self]
  have h1 : HT ρ B (pushS tmp .mark) B1 1 := HT.pushS tmp .mark B ρ
  have h2 : HT ρ B1 (moveWhile lS isNum src tmp) B2 (4 * (intSyms z).length + 2) := by
    refine (ht_moveWhile lS isNum hst (intSyms z) (Sym.sep :: rest) B1 (isNum_intSyms z) rfl
      e1s).of_eq ?_ le_rfl
    rw [e1t]
  have h3 : HT ρ B2 (mv1 lS src dst) B3 2 := by
    refine (ht_mv1 lS hsd B2 Sym.sep rest e2s).of_eq ?_ le_rfl
    rw [e2d]
  have h4 : HT ρ B3 (moveWhile lS isNum tmp dst) B4 (4 * (intSyms z).length + 2) := by
    refine (ht_moveWhile lS isNum hdt.symm ((intSyms z).reverse) (Sym.mark :: B tmp) B3
      (isNum_reverse_intSyms z) rfl e3t).of_eq ?_ (by simp)
    rw [e3d, List.reverse_reverse]
  have h5 : HT ρ B4 (popS tmp) (Function.update B4 tmp (B tmp)) 1 :=
    HT.popS tmp B4 .mark (B tmp) e4t ρ
  refine (HT.seq h1 (HT.seq h2 (HT.seq h3 (HT.seq h4 h5)))).of_eq ?_ (by omega)
  funext j
  simp only [hB4, hB3, hB2, hB1, Function.update_apply]
  split_ifs <;> simp_all

#assert_std_axioms eval_seq_inv eval_peek_inv ht_whileTop_false ht_whileTop_true callI_same'
  cdLoop_closed ht_cdLoop isNum_intSyms mvNum_closed ht_mvNum

end WP.W9c
