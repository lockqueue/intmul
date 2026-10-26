import WP.W9c.PassDefs

/-!
# WP.W9c.PassKit — contract bodies of the pass's sub-programs, call rules, small facts

`PKitOK Mul K C`: every instance of the kit satisfies its contract body (verbatim copies of the
bodies in `WP.W9c.Iface`, `Contracts.Machine.{W3,W5}`) with one constant `C`.
-/

namespace WP.W9c

open TMFw TMFw.Contracts WP.W7k2 IntMul

/-! ## Contract bodies -/

/-- Body of `W9c_blockPack`. -/
def SpecPack (I : Inst 6 24 Unit) (C : ℕ) : Prop :=
  ∀ (k p_in q W B : ℕ) (v : List ℤ) (rx rk ra rb rW : List Sym) (S : Loc 6 I.m → List Sym),
    1 ≤ k → (∀ x ∈ v, bitLen x.natAbs ≤ B) → EndOK rx → TermOK rk → TermOK ra → TermOK rb →
    TermOK rW →
    S (.inl 0) = listSyms v ++ rx → S (.inl 1) = natSyms k ++ rk →
    S (.inl 2) = natSyms p_in ++ ra → S (.inl 3) = natSyms q ++ rb →
    S (.inl 4) = natSyms W ++ rW →
    Runs I.P S (Function.update (Function.update S (.inl 0) (listSyms (v.drop W) ++ rx)) (.inl 5)
        (intSyms (packSignedKronecker ((2 ^ k : ℕ) : ℤ)
          ((v.take W).map (gQuantizeCoordToScale p_in q))) ++ S (.inl 5)))
      (fun _ => True) (C * ((v.take W).length * (B + k + p_in + q + 1) + bitLen W + 1))

/-- Body of `W9c_unpack`. -/
def SpecUnpack (I : Inst 4 24 Unit) (C : ℕ) : Prop :=
  ∀ (k n : ℕ) (Pz : ℤ) (rx rk rn : List Sym) (S : Loc 4 I.m → List Sym),
    1 ≤ k → TermOK rx → TermOK rk → TermOK rn →
    S (.inl 0) = intSyms Pz ++ rx → S (.inl 1) = natSyms k ++ rk →
    S (.inl 2) = natSyms n ++ rn →
    Runs I.P S (Function.update (Function.update S (.inl 0) rx) (.inl 3)
        (listSyms (unpackSignedKronecker ((2 ^ (k - 1) : ℕ) : ℤ) n Pz) ++ S (.inl 3)))
      (fun _ => True) (C * (bitLen Pz.natAbs + n * (k + 1) + 1))

/-- Body of `W9c_window`. -/
def SpecWindow (I : Inst 4 24 Unit) (C : ℕ) : Prop :=
  ∀ (W B : ℕ) (ds ws : List ℤ) (rd rw rW : List Sym) (S : Loc 4 I.m → List Sym),
    ws.length = W → W ≤ ds.length → ds.length ≤ 2 * W →
    (∀ x ∈ ds, bitLen x.natAbs ≤ B) → (∀ x ∈ ws, bitLen x.natAbs ≤ B) →
    EndOK rd → EndOK rw → TermOK rW →
    S (.inl 0) = listSyms ds ++ rd → S (.inl 1) = listSyms ws ++ rw →
    S (.inl 3) = natSyms W ++ rW →
    Runs I.P S (Function.update (Function.update (Function.update S (.inl 0) rd)
        (.inl 1) (listSyms (winStep W ws ds).2 ++ rw))
        (.inl 2) (listSyms (winStep W ws ds).1 ++ S (.inl 2)))
      (fun _ => True) (C * (W * (B + 1) + 1))

/-- Body of `W9c_cycEmit`. -/
def SpecCyc (I : Inst 3 24 Unit) (C : ℕ) : Prop :=
  ∀ (Bc Bv p : ℕ) (cells vs : List ℤ) (rv rL rR : List Sym) (S : Loc 3 I.m → List Sym),
    0 < cells.length → p ≤ cells.length → EndOK rv →
    (∀ v ∈ vs, bitLen v.natAbs ≤ Bv) →
    (∀ j ≤ vs.length, ∀ c ∈ (cycAdd cells.length cells p (vs.take j)).1, bitLen c.natAbs ≤ Bc) →
    S (.inl 0) = listSyms vs ++ rv → S (.inl 1) = tapeL cells p ++ rL →
    S (.inl 2) = tapeR cells p ++ rR →
    Runs I.P S (Function.update (Function.update (Function.update S (.inl 0) rv)
        (.inl 1) (tapeL (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rL))
        (.inl 2) (tapeR (cycAdd cells.length cells p vs).1 (cycAdd cells.length cells p vs).2 ++ rR))
      (fun _ => True)
      (C * (vs.length * (Bv + Bc + 1) +
        (p + vs.length - 1) / cells.length * (cells.length * (Bc + 1)) + 1))

/-- Body of `W5_mulAt Mul`. -/
def SpecMul (Mul : ℕ → ℕ) (I : Inst 3 8 Unit) (C : ℕ) : Prop :=
  ∀ (w : ℕ) (a b : ℤ) (ra rb : List Sym) (S : Loc 3 I.m → List Sym),
    bitLen a.natAbs ≤ w → bitLen b.natAbs ≤ w → TermOK ra → TermOK rb →
    S (.inl 0) = intSyms a ++ ra → S (.inl 1) = intSyms b ++ rb →
    Runs I.P S (Function.update S (.inl 2) (intSyms (a * b) ++ S (.inl 2))) (fun _ => True)
      (C * Mul w + C)

/-- All sub-programs of a pass satisfy their contracts with constant `C`. -/
structure PKitOK {σ : Type} (Mul : ℕ → ℕ) (K : PKit σ) (C : ℕ) : Prop where
  pk : SpecPack K.pk C
  up : SpecUnpack K.up C
  wn : SpecWindow K.wn C
  ce : SpecCyc K.ce C
  mu : SpecMul Mul K.mu C
  cp : SpecCopy K.cp C
  dr : SpecDrop K.dr C
  iz : SpecIsZero K.iz C
  dc : SpecDec K.dc C

/-! ## Three-stack call rule -/

variable {a b : ℕ} {σ : Type}

theorem HT.callI_upd3 {n cap : ℕ} {O : Type} (I : Inst n cap O) (named : List (Loc a b))
    (dflt : Loc a b) (hnd : named.Nodup) (hn : named.length = n) (hcap : cap + n ≤ a + b)
    (l : Lens σ I.R) (B : Loc a b → List Sym) (k₁ k₂ k₃ : Loc n I.m) (v₁ v₂ v₃ : List Sym)
    {Q : I.R → Prop} {T : ℕ}
    (h : Runs I.P (fun x => B (callMap dflt named x))
      (Function.update (Function.update (Function.update (fun x => B (callMap dflt named x))
        k₁ v₁) k₂ v₂) k₃ v₃) Q T)
    (ρ : List (Prog (Loc a b) (fun _ => Sym) σ)) :
    HT ρ B (callI I named dflt l)
      (Function.update (Function.update (Function.update B (callMap dflt named k₁) v₁)
        (callMap dflt named k₂) v₂) (callMap dflt named k₃) v₃) T := by
  have hinj := callMap_injective (m := I.m) dflt named hnd hn (by have := I.hm; omega)
  refine Triple.post (callI_spec I named dflt hnd hn hcap l B h ρ) (fun s hs => ?_)
  obtain ⟨ha, hb, -⟩ := hs
  funext g
  by_cases hg : ∃ x : Loc n I.m, callMap dflt named x = g
  · obtain ⟨x, rfl⟩ := hg
    rw [ha x]
    by_cases hx3 : x = k₃
    · subst hx3; simp
    · rw [Function.update_of_ne hx3, Function.update_of_ne (hinj.ne hx3)]
      by_cases hx2 : x = k₂
      · subst hx2; simp
      · rw [Function.update_of_ne hx2, Function.update_of_ne (hinj.ne hx2)]
        by_cases hx1 : x = k₁
        · subst hx1; simp
        · rw [Function.update_of_ne hx1, Function.update_of_ne (hinj.ne hx1)]
  · push_neg at hg
    rw [hb g hg, Function.update_of_ne (fun e => hg k₃ e.symm),
      Function.update_of_ne (fun e => hg k₂ e.symm), Function.update_of_ne (fun e => hg k₁ e.symm)]

/-! ## Small facts -/

theorem endOK_mark (l : List Sym) : EndOK (Sym.mark :: l) := fun x hx => by
  simp only [List.head?_cons, Option.some.injEq] at hx
  subst hx
  exact ⟨by decide, by decide⟩

theorem endOK_listSyms_cons (vs : List ℤ) (l : List Sym) (h : EndOK l) :
    EndOK (listSyms vs ++ l) ∨ vs ≠ [] := by
  cases vs with
  | nil => left; simpa [listSyms] using h
  | cons _ _ => right; simp

theorem termOK_listSyms (vs : List ℤ) (l : List Sym) (hl : TermOK l) : TermOK (listSyms vs ++ l) := by
  cases vs with
  | nil => simpa [listSyms] using hl
  | cons v vs =>
    simp only [listSyms, List.flatMap_cons, List.append_assoc]
    exact termOK_intSyms v _

theorem length_unpack (H : ℤ) : ∀ (n : ℕ) (C : ℤ), (unpackSignedKronecker H n C).length = n
  | 0, _ => rfl
  | n + 1, C => by simp [unpackSignedKronecker, length_unpack H n]

theorem listSyms_nil : listSyms [] = [] := rfl

theorem listSyms_cons (v : ℤ) (vs : List ℤ) :
    listSyms (v :: vs) = intSyms v ++ Sym.sep :: listSyms vs := by
  simp [listSyms]

theorem listSyms_append (l1 l2 : List ℤ) : listSyms (l1 ++ l2) = listSyms l1 ++ listSyms l2 := by
  simp [listSyms]

theorem isSgn_head_listSyms (v : ℤ) (vs : List ℤ) (l : List Sym) :
    optT isSgn (listSyms (v :: vs) ++ l).head? = true := by
  rw [listSyms_cons]
  simp only [intSyms, List.cons_append, List.head?_cons, optT, sgnSym]
  split <;> rfl

theorem isSgn_head_endOK (l : List Sym) (h : EndOK l) : optT isSgn l.head? = false := by
  cases l with
  | nil => rfl
  | cons x l =>
    obtain ⟨h1, h2⟩ := h x rfl
    simp only [List.head?_cons, optT]
    cases x <;> simp_all [isSgn]

theorem cycAdd_length (r : ℕ) : ∀ (cells : List ℤ) (p : ℕ) (vs : List ℤ),
    (cycAdd r cells p vs).1.length = cells.length
  | _, _, [] => rfl
  | cells, p, v :: vs => by
    simp only [cycAdd]
    rw [cycAdd_length]
    simp

theorem cycAdd_append (r : ℕ) : ∀ (cells : List ℤ) (p : ℕ) (l1 l2 : List ℤ),
    cycAdd r cells p (l1 ++ l2) = cycAdd r (cycAdd r cells p l1).1 (cycAdd r cells p l1).2 l2
  | _, _, [], _ => rfl
  | cells, p, v :: l1, l2 => by
    simp only [List.cons_append, cycAdd]
    exact cycAdd_append r _ _ l1 l2

#assert_std_axioms HT.callI_upd3 endOK_mark termOK_listSyms length_unpack listSyms_cons
  listSyms_append isSgn_head_listSyms isSgn_head_endOK cycAdd_length cycAdd_append

end WP.W9c
