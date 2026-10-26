import WP.W9s.DealDS

/-!
# WP.W9s.Rec — the recursive procedure and its building blocks

`fft K = fix (fftBody K)`. A call transforms the block on top of `sA` (`2^n` rows, followed by
`symBlk`), with the combine step `Δ` on top of `sDS`:
1. move row 0 to `sE`; if `symBlk` follows, the block had one row: move it back and return;
2. otherwise deal the remaining rows in pairs (`dealLoop`): even rows on `sE`, odd rows on `sO`;
3. put the evens, then the odds, back on `sA` as two blocks; push the doubled step `2Δ`;
4. recurse on the odds; park the result on `sD`; recurse on the evens; pop `2Δ`;
5. combine (`WP.W9s.Combine`).
No register is live across `recur 0`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

/-- Deal the rows of the block on `sA` in pairs. -/
def dealLoop (K : Kit) : MProg K :=
  whileTop (lS K) sA (notS symBlk) (.seq (mvRow (lS K) sA sE) (mvRow (lS K) sA sO))

/-- Push a doubled copy of the top step block of `sDS`. -/
def dsDouble (K : Kit) : MProg K :=
  .seq (pushS sT symG) <| .seq (pushS sT2 symG) <|
  .seq (uMove (lS K) sDS sT) <|
  .seq (uDup (lS K) sT sDS sT2) <|
  .seq (popS sT) <| .seq (pushS sDS symG) <|
  .seq (uMove (lS K) sT2 sDS) (popS sT2)

/-- Drop the top step block of `sDS`. -/
def dsPop (K : Kit) : MProg K := dropTo (lS K) sDS symG

/-- The body of the recursive procedure. -/
def fftBody (K : Kit) : MProg K :=
  .seq (pushS sE symG) <| .seq (pushS sO symG) <|
  .seq (mvRow (lS K) sA sE) <|
  .seq (peekL (lS K) sA) <|
  .ite (fun v => decide ((lS K).get v = some symBlk))
    (.seq (rwP K sE sA symG) (popS sO)) <|
  .seq (mvRow (lS K) sA sO) <|
  .seq (dealLoop K) <|
  .seq (rwP K sE sA symG) <|
  .seq (pushS sA symBlk) <|
  .seq (rwP K sO sA symG) <|
  .seq (dsDouble K) <|
  .seq (.recur 0) <|
  .seq (pushS sT symG) <|
  .seq (rwP K sA sT symBlk) <|
  .seq (pushS sD symBlk) <|
  .seq (rwP K sT sD symG) <|
  .seq (.recur 0) <|
  .seq (dsPop K) (combine K)

/-- The recursive procedure. -/
def fft (K : Kit) : MProg K := .fix (fftBody K)

theorem dealLoop_closed (K : Kit) : (dealLoop K).Closed :=
  whileTop_closed _ _ _ ⟨mvRow_closed _ _ _, mvRow_closed _ _ _⟩

theorem dsDouble_closed (K : Kit) : (dsDouble K).Closed :=
  ⟨trivial, trivial, uMove_closed _ _ _, uDup_closed _ _ _ _, trivial, trivial, uMove_closed _ _ _,
    trivial⟩

theorem freeBelow_mono {σ : Type} :
    ∀ (p : Prog Host (fun _ => Sym) σ) {d d' : ℕ}, d ≤ d' → p.FreeBelow d → p.FreeBelow d'
  | .push _ _, _, _, _, _ => trivial
  | .peek _ _, _, _, _, _ => trivial
  | .pop _ _, _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hpq => ⟨freeBelow_mono p h hpq.1, freeBelow_mono q h hpq.2⟩
  | .ite _ p q, _, _, h, hpq => ⟨freeBelow_mono p h hpq.1, freeBelow_mono q h hpq.2⟩
  | .loop _ p, _, _, h, hp => freeBelow_mono p h hp
  | .fix b, _, _, h, hb => freeBelow_mono b (by omega) hb
  | .recur n, _, _, h, hn => by
    simp only [Prog.FreeBelow] at hn ⊢
    omega

theorem fft_closed {K : Kit} {CH : ℕ} (hH : HalveSpec K.Hp CH) : (fft K).Closed := by
  have m : ∀ {p : MProg K}, p.Closed → p.FreeBelow 1 := fun h => freeBelow_mono _ (Nat.zero_le 1) h
  show (fftBody K).FreeBelow 1
  exact ⟨trivial, trivial, m (mvRow_closed _ _ _), trivial, ⟨m (rwP_closed _ _ _ _), trivial⟩,
    m (mvRow_closed _ _ _), m (dealLoop_closed K), m (rwP_closed _ _ _ _), trivial,
    m (rwP_closed _ _ _ _), m (dsDouble_closed K), (by decide : (0 : ℕ) < 1), trivial,
    m (rwP_closed _ _ _ _), trivial, m (rwP_closed _ _ _ _), (by decide : (0 : ℕ) < 1),
    m (dropTo_closed _ _ _), m (combine_closed hH)⟩

/-! ## List facts -/

theorem evensL_cons_cons {α : Type} (x y : α) (l : List α) : evensL (x :: y :: l) = x :: evensL l :=
  rfl

theorem oddsL_cons_cons {α : Type} (x y : α) (l : List α) : oddsL (x :: y :: l) = y :: oddsL l :=
  rfl

theorem length_evensL {α : Type} : ∀ l : List α, (evensL l).length = (l.length + 1) / 2
  | [] => by simp [evensL]
  | [_] => by simp [evensL]
  | _ :: _ :: l => by
    simp only [evensL_cons_cons, List.length_cons, length_evensL l]
    omega

theorem length_oddsL {α : Type} : ∀ l : List α, (oddsL l).length = l.length / 2
  | [] => by simp [oddsL]
  | [_] => by simp [oddsL]
  | _ :: _ :: l => by
    simp only [oddsL_cons_cons, List.length_cons, length_oddsL l]
    omega

theorem mem_evensL {α : Type} {x : α} : ∀ {l : List α}, x ∈ evensL l → x ∈ l
  | [], h => by simp [evensL] at h
  | [_], h => by simpa [evensL] using h
  | _ :: _ :: l, h => by
    rw [evensL_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_evensL h))

theorem mem_oddsL {α : Type} {x : α} : ∀ {l : List α}, x ∈ oddsL l → x ∈ l
  | [], h => by simp [oddsL] at h
  | [_], h => by simp [oddsL] at h
  | _ :: _ :: l, h => by
    rw [oddsL_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_oddsL h))

theorem symBlk_not_mem_blkR (X : List (List (ℤ × ℤ))) : symBlk ∉ blkR X := by
  intro h
  rcases mem_blkR h with h1 | h1
  · exact Bool.false_ne_true h1.symm
  · cases h1

theorem symG_not_mem_rev_rowE (x : List (ℤ × ℤ)) : symG ∉ (rowE x).reverse := by
  intro h
  have h' := List.mem_reverse.mp h
  rw [rowE, List.mem_append] at h'
  rcases h' with h' | h'
  · exact tag_not_mem_es rfl x h'
  · cases List.mem_singleton.mp h'

#assert_std_axioms dealLoop_closed dsDouble_closed freeBelow_mono fft_closed evensL_cons_cons oddsL_cons_cons
  length_evensL length_oddsL mem_evensL mem_oddsL symBlk_not_mem_blkR symG_not_mem_rev_rowE

end WP.W9s
