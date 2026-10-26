import WP.W9a.Glue
import Contracts.W9.Levels

/-!
# WP.W9a.LevelBase — shared scaffolding of the three level programs

* Registers `Rs × (Rx × Option Sym)`: the sweep (first), the RET operation (second), the glue
  symbol register (third); lifts `liftS3`, `liftX3`, `liftG3` with their evaluation lemmas.
* List lemmas for node indices (`drop_cons_of_lt`, `take_succ_of_drop`, `flatMap_range_getD`).
* Glue scratch `tA` (scratch 0) and `tB` (scratch 1, the body counter).
* The state family `trtl hm S0 tr tl kb` (only `TR`, `TL`, `tB` changed) and its step lemmas, from
  which the body skips are assembled; `setC2one`, `cleanup` (drop the group size and the header).
-/

namespace WP.W9a

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

/-! ## Registers -/

section Lift3

variable {K Rs Rx : Type}

/-- The sweep component. -/
def liftS3 (p : Prog K (fun _ => Sym) Rs) : Prog K (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  p.liftRegs (Lens.fst Rs (Rx × Option Sym))

/-- The RET-operation component. -/
def liftX3 (p : Prog K (fun _ => Sym) Rx) : Prog K (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  p.liftRegs ((Lens.snd Rs (Rx × Option Sym)).comp (Lens.fst Rx (Option Sym)))

/-- The glue (one symbol register). -/
def liftG3 (p : SProg K) : Prog K (fun _ => Sym) (Rs × (Rx × Option Sym)) :=
  p.liftRegs ((Lens.snd Rs (Rx × Option Sym)).comp (Lens.snd Rx (Option Sym)))

theorem closed_liftS3 {p : Prog K (fun _ => Sym) Rs} (h : p.Closed) :
    (liftS3 (Rx := Rx) p).Closed := closed_liftRegs _ h

theorem closed_liftX3 {p : Prog K (fun _ => Sym) Rx} (h : p.Closed) :
    (liftX3 (Rs := Rs) p).Closed := closed_liftRegs _ h

theorem closed_liftG3 {p : SProg K} (h : p.Closed) : (liftG3 (Rs := Rs) (Rx := Rx) p).Closed :=
  closed_liftRegs _ h

variable [DecidableEq K]

theorem liftS3_eval {p : Prog K (fun _ => Sym) Rs} {s s' : St K (fun _ => Sym) Rs} {t : ℕ}
    (h : Eval [] p s s' t) (b : Rx × Option Sym) :
    Eval [] (liftS3 p) ⟨(s.var, b), s.stk⟩ ⟨(s'.var, b), s'.stk⟩ t :=
  Eval.liftRegs _ h (s.var, b) rfl

theorem liftX3_eval {p : Prog K (fun _ => Sym) Rx} {s s' : St K (fun _ => Sym) Rx} {t : ℕ}
    (h : Eval [] p s s' t) (a : Rs) (q : Option Sym) :
    Eval [] (liftX3 p) ⟨(a, (s.var, q)), s.stk⟩ ⟨(a, (s'.var, q)), s'.stk⟩ t :=
  Eval.liftRegs _ h (a, (s.var, q)) rfl

theorem liftG3_eval {p : SProg K} {S S' : K → List Sym} {r r' : Option Sym} {t : ℕ}
    (h : Eval [] p ⟨r, S⟩ ⟨r', S'⟩ t) (a : Rs) (x : Rx) :
    Eval [] (liftG3 p) ⟨(a, (x, r)), S⟩ ⟨(a, (x, r')), S'⟩ t :=
  Eval.liftRegs _ h (a, (x, r)) rfl

end Lift3

/-! ## Node indices -/

theorem drop_cons_of_lt {α : Type} (d : α) : ∀ (xs : List α) (i : ℕ), i < xs.length →
    ∃ x, xs.drop i = x :: xs.drop (i + 1) ∧ xs.getD i d = x ∧ x ∈ xs
  | [], i, h => by simp at h
  | x :: xs, 0, _ => ⟨x, rfl, rfl, List.mem_cons_self ..⟩
  | x :: xs, i + 1, h => by
    obtain ⟨y, h1, h2, h3⟩ := drop_cons_of_lt d xs i (by simpa using h)
    exact ⟨y, by simpa using h1, by simpa using h2, List.mem_cons_of_mem _ h3⟩

theorem take_succ_of_drop {α : Type} : ∀ (xs : List α) (i : ℕ) (x : α) (l : List α),
    xs.drop i = x :: l → xs.take (i + 1) = xs.take i ++ [x]
  | [], i, x, l, h => by simp at h
  | y :: xs, 0, x, l, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    simp [h.1]
  | y :: xs, i + 1, x, l, h => by
    simp only [List.drop_succ_cons] at h
    simp [List.take_succ_cons, take_succ_of_drop xs i x l h]

theorem map_getD_range {α : Type} (d : α) : ∀ xs : List α,
    (List.range xs.length).map (fun i => xs.getD i d) = xs
  | [] => rfl
  | x :: xs => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    have h : ((fun i => (x :: xs).getD i d) ∘ Nat.succ) = fun i => xs.getD i d := by
      funext i
      simp
    rw [h, map_getD_range d xs]
    simp

theorem flatMap_map' {α β γ : Type} (f : α → β) (g : β → List γ) :
    ∀ l : List α, (l.map f).flatMap g = l.flatMap (fun a => g (f a))
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, flatMap_map' f g l]

theorem flatMap_range_getD {α β : Type} (d : α) (f : α → List β) (xs : List α) :
    (List.range xs.length).flatMap (fun i => f (xs.getD i d)) = xs.flatMap f := by
  rw [← flatMap_map', map_getD_range]

theorem groupAt_one_of_drop (xs : List (Array (ℤ × ℤ))) (i : ℕ) (x : Array (ℤ × ℤ))
    (hx : xs.drop i = x :: xs.drop (i + 1)) : groupAt 1 xs i = [x] := by
  rw [groupAt, Nat.mul_one, hx]
  rfl

/-! ## Glue scratch and the `TR`/`TL`/`tB` state family -/

section Family

variable {m : ℕ}

/-- Glue temporary (scratch 0). -/
def tA (hm : 4 ≤ m) : BLoc m := .inr ⟨0, by omega⟩

/-- Body counter (scratch 1). -/
def tB (hm : 4 ≤ m) : BLoc m := .inr ⟨1, by omega⟩

/-- `S0` with `TR`, `TL` and `tB` replaced. -/
def trtl (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) : BLoc m → List Sym :=
  Function.update (Function.update (Function.update S0 (.inl .TR) tr) (.inl .TL) tl) (tB hm) kb

theorem trtl_self (hm : 4 ≤ m) (S0 : BLoc m → List Sym) :
    trtl hm S0 (S0 (.inl .TR)) (S0 (.inl .TL)) (S0 (tB hm)) = S0 := by
  simp [trtl]

theorem trtl_other (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) (k : BLoc m)
    (h1 : k ≠ .inl .TR) (h2 : k ≠ .inl .TL) (h3 : k ≠ tB hm) : trtl hm S0 tr tl kb k = S0 k := by
  simp [trtl, h1, h2, h3]

theorem trtl_TR (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) :
    trtl hm S0 tr tl kb (.inl .TR) = tr := by simp [trtl, tB]

theorem trtl_TL (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) :
    trtl hm S0 tr tl kb (.inl .TL) = tl := by simp [trtl, tB]

theorem trtl_tB (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) :
    trtl hm S0 tr tl kb (tB hm) = kb := by simp [trtl]

theorem pushC_tB_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) (x : Sym)
    (v : Option Sym) :
    Eval [] (pushC (tB hm) x) ⟨v, trtl hm S0 tr tl kb⟩ ⟨v, trtl hm S0 tr tl (x :: kb)⟩ 1 := by
  refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
  simp [trtl]

theorem popR_tB_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym) (x : Sym)
    (v : Option Sym) :
    Eval [] (popR (tB hm)) ⟨v, trtl hm S0 tr tl (x :: kb)⟩ ⟨some x, trtl hm S0 tr tl kb⟩ 1 := by
  refine (Eval.pop [] (tB hm) (fun _ o => o) _ _).of_eq ?_ rfl
  rw [trtl_tB]
  simp [trtl]

theorem moveChunk_trtl_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (d tr tl kb : List Sym)
    (hd : symSub ∉ d) (v : Option Sym) :
    Eval [] (moveChunk (.inl .TR) (.inl .TL) symSub) ⟨v, trtl hm S0 (d ++ symSub :: tr) tl kb⟩
      ⟨some symSub, trtl hm S0 tr ((d ++ [symSub]).reverse ++ tl) kb⟩ (3 * d.length + 3) := by
  refine (moveChunk_eval (by simp) symSub v d tr _ hd (trtl_TR hm S0 _ tl kb)).of_eq ?_ rfl
  congr 1
  funext k
  simp only [trtl, Function.update_apply]
  split_ifs <;> simp_all [tB]

theorem chunkLoop_trtl_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (cs : List (List Sym))
    (hcs : ∀ c ∈ cs, symSub ∉ c) (tr tl rK : List Sym) (hrK : TermOK rK) (v : Option Sym) :
    ∃ v', Eval [] (countLoop (tB hm) (tA hm) (moveChunk (.inl .TR) (.inl .TL) symSub))
      ⟨v, trtl hm S0 (cs.flatMap (· ++ [symSub]) ++ tr) tl (natSyms cs.length ++ rK)⟩
      ⟨v', trtl hm S0 tr ((cs.flatMap (· ++ [symSub])).reverse ++ tl) rK⟩
      (incSeqCost 6 10 cs.length + 3 * (cs.flatMap (· ++ [symSub])).length + 2) := by
  obtain ⟨v', e⟩ := chunkLoop_eval (Kc := tB hm) (t := tA hm) (src := .inl .TR) (dst := .inl .TL)
    (by simp [tB, tA]) (by simp) (by simp [tB]) (by simp [tB]) symSub cs hcs tr rK hrK _ v
    (trtl_TR hm S0 _ _ _) (trtl_tB hm S0 _ _ _)
  refine ⟨v', e.of_eq ?_ rfl⟩
  congr 1
  funext k
  simp only [trtl, Function.update_apply]
  split_ifs <;> simp_all [tB]

theorem copyFieldAt_trtl_eval (hm : 4 ≤ m) (S0 : BLoc m → List Sym) (tr tl kb : List Sym)
    (pre : List ℕ) (f : ℕ) (rest : List Sym)
    (hC0 : S0 (.inl .C0) = hdrSyms pre ++ natSyms f ++ Sym.mark :: rest) (v : Option Sym) :
    Eval [] (copyFieldAt pre.length (.inl .C0) (tB hm) (tA hm) (.tag 1))
      ⟨v, trtl hm S0 tr tl kb⟩ ⟨some (.tag 1), trtl hm S0 tr tl (natSyms f ++ kb)⟩
      (6 * (hdrSyms pre).length + 7 * bitLen f + 11) := by
  refine (copyFieldAt_eval (by simp [tB]) (by simp [tA]) (by simp [tA, tB]) 1 pre f rest _ v
    (by rw [trtl_other hm S0 tr tl kb _ (by simp) (by simp) (by simp [tB]), hC0])).of_eq ?_ rfl
  congr 1
  funext k
  simp only [trtl, Function.update_apply]
  split_ifs <;> simp_all [tB]

end Family

/-! ## Group size and cleanup -/

section Cleanup

variable {m : ℕ}

/-- `C2 := natSyms 1 ++ mark :: C2` (the sweep group size `g = 1`). -/
def setC2one : SProg (BLoc m) := .seq (pushC (.inl .C2) .mark) (pushC (.inl .C2) (.bit true))

theorem setC2one_eval (S0 : BLoc m → List Sym) (v : Option Sym) :
    Eval [] setC2one ⟨v, S0⟩
      ⟨v, Function.update S0 (.inl .C2) (natSyms 1 ++ Sym.mark :: S0 (.inl .C2))⟩ 2 := by
  have e1 : Eval [] (pushC (.inl .C2) .mark) ⟨v, S0⟩
      ⟨v, Function.update S0 (.inl .C2) (.mark :: S0 (.inl .C2))⟩ 1 := Eval.push _ _ _ _ _
  have e2 : Eval [] (pushC (.inl .C2) (.bit true))
      ⟨v, Function.update S0 (.inl .C2) (.mark :: S0 (.inl .C2))⟩
      ⟨v, Function.update S0 (.inl .C2) (natSyms 1 ++ Sym.mark :: S0 (.inl .C2))⟩ 1 := by
    refine (Eval.push _ _ _ _ _).of_eq ?_ rfl
    rw [Function.update_self, Function.update_idem, natSyms_one]
    rfl
  exact Eval.seq e1 e2

/-- Drop the group size from `C2` and the header from `C0` (both above their guards). -/
def cleanup : SProg (BLoc m) :=
  .seq (dropUntil (.inl .C2) (isSym .mark)) (dropUntil (.inl .C0) (isSym symGuard))

theorem cleanup_eval (S0 : BLoc m → List Sym) (v : Option Sym) (g : ℕ) (fs : List ℕ)
    (c2 c0 : List Sym) (hC2 : S0 (.inl .C2) = natSyms g ++ Sym.mark :: c2)
    (hC0 : S0 (.inl .C0) = hdrSyms fs ++ symGuard :: c0) :
    Eval [] cleanup ⟨v, S0⟩
      ⟨some symGuard, Function.update (Function.update S0 (.inl .C2) c2) (.inl .C0) c0⟩
      (2 * bitLen g + 2 * (hdrSyms fs).length + 4) := by
  have hg : ∀ x ∈ natSyms g, isSym .mark (some x) = false := by
    intro x hx
    simp only [natSyms, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact isSym_some_of_ne (fun h => by cases h)
  have hf : ∀ x ∈ hdrSyms fs, isSym symGuard (some x) = false := by
    intro x hx
    refine isSym_some_of_ne (fun e => tag_not_mem_hdrSyms 7 fs ?_)
    rw [e] at hx
    exact hx
  have e1 := dropUntil_eval (isSym .mark) v (natSyms g) (Sym.mark :: c2) S0 hg (isSym_some_self _) hC2
  have hC0' : Function.update S0 (.inl .C2) c2 (.inl .C0) = hdrSyms fs ++ symGuard :: c0 := by
    rw [Function.update_of_ne (by simp), hC0]
  have e2 := dropUntil_eval (src := (.inl .C0 : BLoc m)) (isSym symGuard) (some Sym.mark)
    (hdrSyms fs) (symGuard :: c0) (Function.update S0 (.inl .C2) c2) hf (isSym_some_self _) hC0'
  refine (Eval.seq e1 e2).of_eq rfl ?_
  rw [length_natSyms]
  omega

theorem closed_setC2one : (setC2one : SProg (BLoc m)).Closed := ⟨trivial, trivial⟩

theorem closed_cleanup : (cleanup : SProg (BLoc m)).Closed :=
  ⟨closed_dropUntil _ _, closed_dropUntil _ _⟩

end Cleanup

/-! ## Symbol facts for table bodies -/

theorem symSub_not_mem_tapSyms (t : ℤ) : symSub ∉ tapSyms t := by
  intro h
  rw [tapSyms, List.mem_append, List.mem_singleton] at h
  rcases h with h | h
  · have := entrySym_intSyms t _ h
    simp [EntrySym, isTagSym, symSub] at this
  · exact absurd h (by decide)

theorem symSub_not_mem_taps (taps : List ℤ) : symSub ∉ taps.flatMap tapSyms := by
  intro h
  obtain ⟨t, -, ht⟩ := List.mem_flatMap.1 h
  exact symSub_not_mem_tapSyms t ht

theorem symSub_not_mem_entries (f : ℕ → ℤ × ℤ) (n : ℕ) :
    symSub ∉ (List.range n).flatMap (fun k => entrySyms (f k)) := by
  intro h
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
  exact tag_not_mem_entrySyms 6 _ hk

theorem twSyms_eq (n : ℕ) (tw : Array (ℤ × ℤ)) :
    twSyms n tw = (List.range n).flatMap (fun k => entrySyms (IntMul.read1D tw k)) ++ [symSub] :=
  rfl

theorem length_chunks_le (x : Sym) : ∀ cs : List (List Sym),
    cs.length ≤ (cs.flatMap (· ++ [x])).length
  | [] => le_rfl
  | c :: cs => by
    have := length_chunks_le x cs
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

#assert_std_axioms liftS3_eval liftX3_eval liftG3_eval drop_cons_of_lt take_succ_of_drop
  map_getD_range flatMap_range_getD groupAt_one_of_drop trtl_self trtl_other pushC_tB_eval
  popR_tB_eval moveChunk_trtl_eval chunkLoop_trtl_eval copyFieldAt_trtl_eval setC2one_eval
  cleanup_eval symSub_not_mem_taps symSub_not_mem_entries length_chunks_le


/-! ## Header with `g = 1`, node sizes -/

section HdrOne

variable {m : ℕ}

/-- Read a segment header onto `C0` and set the group size `g = 1` on `C2`. -/
def hdrOne (n : ℕ) (hm : 4 ≤ m) : SProg (BLoc m) :=
  .seq (readHdr n (.inl .TR) (.inl .TL) (.inl .C0) (tA hm)) setC2one

theorem closed_hdrOne (n : ℕ) (hm : 4 ≤ m) : (hdrOne n hm).Closed :=
  ⟨closed_readHdr _ _ _ _ _, closed_setC2one⟩

theorem hdrOne_eval (hm : 4 ≤ m) (tag : Sym) (fs : List ℕ) (rest : List Sym)
    (S0 : BLoc m → List Sym) (v : Option Sym) (hTR : S0 (.inl .TR) = tag :: (hdrSyms fs ++ rest)) :
    Eval [] (hdrOne fs.length hm) ⟨v, S0⟩
      ⟨some symLevel, Function.update (Function.update (Function.update (Function.update S0
        (.inl .TR) rest) (.inl .TL) ((hdrSyms fs).reverse ++ tag :: S0 (.inl .TL))) (.inl .C0)
        (hdrSyms fs ++ symGuard :: S0 (.inl .C0))) (.inl .C2)
        (natSyms 1 ++ Sym.mark :: S0 (.inl .C2))⟩ (7 * (hdrSyms fs).length + 9) := by
  have e1 := readHdr_eval (TR := (.inl .TR : BLoc m)) (TL := .inl .TL) (C0 := .inl .C0)
    (tA := tA hm) (by simp) (by simp) (by simp [tA]) (by simp) (by simp [tA]) (by simp [tA])
    tag fs rest S0 v hTR
  have e2 := setC2one_eval (Function.update (Function.update (Function.update S0 (.inl .TR) rest)
    (.inl .TL) ((hdrSyms fs).reverse ++ tag :: S0 (.inl .TL))) (.inl .C0)
    (hdrSyms fs ++ symGuard :: S0 (.inl .C0))) (some symLevel)
  refine (Eval.seq e1 e2).of_eq ?_ rfl
  rw [Function.update_of_ne (by simp), Function.update_of_ne (by simp),
    Function.update_of_ne (by simp)]

end HdrOne

theorem groupSyms_singleton (x : Array (ℤ × ℤ)) : groupSyms [x] = blkE x.toList := by
  rw [groupSyms_cons, groupSyms_nil, List.append_nil]

theorem groupSyms_length_le (w n : ℕ) : ∀ xs : List (Array (ℤ × ℤ)),
    (∀ x ∈ xs, x.size = n ∧ ArrW w x) → (groupSyms xs).length ≤ xs.length * (n * eb w)
  | [], _ => by simp [groupSyms_nil]
  | x :: xs, h => by
    obtain ⟨hs, hw⟩ := h x (List.mem_cons_self ..)
    have hlen : x.toList.length = n := by rw [Array.length_toList, hs]
    have h1 := length_blkE_le w x.toList hw
    rw [hlen] at h1
    have h2 := groupSyms_length_le w n xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    rw [groupSyms_cons, List.length_append, List.length_cons, Nat.succ_mul]
    omega

#assert_std_axioms hdrOne_eval groupSyms_singleton groupSyms_length_le

end WP.W9a
