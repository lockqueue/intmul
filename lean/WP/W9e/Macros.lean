import WP.W9e.Kit
import Contracts.W9.Common

/-!
# WP.W9e.Macros — symbol-register macros of the POST routing phases

New macros (exact `Eval` lemmas, any procedure environment `ρ`):

| macro | effect | cost |
|---|---|---|
| `moveTo stop src dst` | `src = d ++ stop :: rest` (`stop ∉ d`) ↦ `src = rest`, `dst = dᴿ ++ dst`, reg `= stop` | `3·|d| + 2` |
| `moveThrough stop src dst` | as `moveTo`, then `stop` pushed on `dst` | `3·|d| + 3` |
| `dropBits k` | pop the bit block on top of `k` (terminator kept) | `3·|blk| + 2` |
| `fetchField src dst tmp i` | copy field `i` of the header `hdrSyms fs` on `src` onto `dst` | `≤ 12·|hdrSyms fs|` |

Then the `Runs` forms of these and of the library macros used by the phases (`rs_*`), through an
arbitrary register lens `l : Lens σ (Option Sym)`.
-/

namespace WP.W9e

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

section Defs

variable {K : Type}

/-- Move symbols from `src` onto `dst` (reversed) up to the first `stop`; the `stop` is popped
into the register. -/
def moveTo (stop : Sym) (src dst : K) : SProg K :=
  .seq (popR src) (.loop (fun r => decide (r ≠ some stop)) (.seq (pushR dst) (popR src)))

/-- `moveTo`, then push the `stop` onto `dst`. -/
def moveThrough (stop : Sym) (src dst : K) : SProg K := .seq (moveTo stop src dst) (pushR dst)

/-- Loop body of `dropBits`: pop, then look at the next symbol. -/
def dropBody (k : K) : SProg K := .seq (.pop k fun r _ => r) (peekR k)

/-- Pop the bit block on top of `k`; its terminator stays on `k`. -/
def dropBits (k : K) : SProg K := .seq (peekR k) (.loop optIsBit (dropBody k))

/-- Copy field `i` of the header `hdrSyms fs` on `src` onto `dst`. The fields before it are moved
to `tmp` and back; `tmp` must have a non-bit symbol (or the bottom) on top. -/
def fetchField (src dst tmp : K) : ℕ → SProg K
  | 0 => copyBlock src dst tmp
  | i + 1 => .seq (moveBlock src tmp) (.seq (popR src) (.seq (pushR tmp)
      (.seq (fetchField src dst tmp i) (.seq (popR tmp) (.seq (pushR src) (moveBlock tmp src))))))

end Defs

section Evals

variable {K : Type} [DecidableEq K]

theorem eval_push' (ρ : List (SProg K)) (k : K) (f : Option Sym → Sym) (v : Option Sym)
    (S S' : K → List Sym) (h : Function.update S k (f v :: S k) = S') :
    Eval ρ (.push k f) ⟨v, S⟩ ⟨v, S'⟩ 1 :=
  (Eval.push ρ k f v S).of_eq (by rw [h]) rfl

theorem eval_pop' (ρ : List (SProg K)) (k : K) (f : Option Sym → Option Sym → Option Sym)
    (v : Option Sym) (S S' : K → List Sym) (x : Sym) (tl : List Sym) (hk : S k = x :: tl)
    (h : Function.update S k tl = S') :
    Eval ρ (.pop k f) ⟨v, S⟩ ⟨f v (some x), S'⟩ 1 := by
  have e := Eval.pop ρ k f v S
  rw [hk] at e
  exact e.of_eq (by rw [← h]; rfl) rfl

theorem eval_peek' (ρ : List (SProg K)) (k : K) (f : Option Sym → Option Sym → Option Sym)
    (v : Option Sym) (S : K → List Sym) (o : Option Sym) (hk : (S k).head? = o) :
    Eval ρ (.peek k f) ⟨v, S⟩ ⟨f v o, S⟩ 1 :=
  (Eval.peek ρ k f v S).of_eq (by rw [hk]) rfl

theorem moveTo_loop_eval {src dst : K} (hne : src ≠ dst) (stop : Sym) (ρ : List (SProg K)) :
    ∀ (d rest : List Sym) (S : K → List Sym), stop ∉ d → S src = (d ++ stop :: rest).tail →
      Eval ρ (.loop (fun r => decide (r ≠ some stop)) (.seq (pushR dst) (popR src)))
        ⟨(d ++ stop :: rest).head?, S⟩
        ⟨some stop, Function.update (Function.update S src rest) dst (d.reverse ++ S dst)⟩
        (3 * d.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp)).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some stop, S⟩ : SSt K) =
      ⟨some stop, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: d, rest, S, hd, hS => by
    have hx : x ≠ stop := fun h => hd (by simp [h])
    have hd' : stop ∉ d := fun h => hd (List.mem_cons_of_mem _ h)
    have hS' : S src = d ++ stop :: rest := hS
    have hpush : Eval ρ (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      (Eval.push ρ dst (fun r => r.getD .sep) (some x) S).of_eq rfl rfl
    have hsrc : Function.update S dst (x :: S dst) src = d ++ stop :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval ρ (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(d ++ stop :: rest).head?, Function.update (Function.update S dst (x :: S dst)) src
          (d ++ stop :: rest).tail⟩ 1 := by
      refine (Eval.pop ρ src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveTo_loop_eval hne stop ρ d rest
      (Function.update (Function.update S dst (x :: S dst)) src (d ++ stop :: rest).tail) hd'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simpa using hx) (Eval.seq hpush hpop) ih).of_eq ?_
      (by simp only [List.length_cons]; omega)
    congr 1
    funext k
    simp only [Function.update_apply, List.reverse_cons, List.append_assoc, List.singleton_append]
    split_ifs <;> simp_all

/-- **moveTo**, exact. -/
theorem moveTo_eval {src dst : K} (hne : src ≠ dst) (stop : Sym) (ρ : List (SProg K))
    (v : Option Sym) (d rest : List Sym) (S : K → List Sym) (hd : stop ∉ d)
    (hS : S src = d ++ stop :: rest) :
    Eval ρ (moveTo stop src dst) ⟨v, S⟩
      ⟨some stop, Function.update (Function.update S src rest) dst (d.reverse ++ S dst)⟩
      (3 * d.length + 2) := by
  have h1 : Eval ρ (popR src) ⟨v, S⟩ ⟨(d ++ stop :: rest).head?,
      Function.update S src (d ++ stop :: rest).tail⟩ 1 := by
    refine (Eval.pop ρ src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveTo_loop_eval hne stop ρ d rest (Function.update S src (d ++ stop :: rest).tail)
    hd (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

/-- **moveThrough**, exact. -/
theorem moveThrough_eval {src dst : K} (hne : src ≠ dst) (stop : Sym) (ρ : List (SProg K))
    (v : Option Sym) (d rest : List Sym) (S : K → List Sym) (hd : stop ∉ d)
    (hS : S src = d ++ stop :: rest) :
    Eval ρ (moveThrough stop src dst) ⟨v, S⟩
      ⟨some stop, Function.update (Function.update S src rest) dst (stop :: (d.reverse ++ S dst))⟩
      (3 * d.length + 3) := by
  have h1 := moveTo_eval hne stop ρ v d rest S hd hS
  set S1 := Function.update (Function.update S src rest) dst (d.reverse ++ S dst) with hS1
  have h2 : Eval ρ (pushR dst) ⟨some stop, S1⟩
      ⟨some stop, Function.update S1 dst (stop :: S1 dst)⟩ 1 :=
    (Eval.push ρ dst (fun r => r.getD .sep) (some stop) S1).of_eq rfl rfl
  refine (Eval.seq h1 h2).of_eq ?_ rfl
  rw [hS1, Function.update_self, Function.update_idem]

theorem dropBits_loop_eval (k : K) (ρ : List (SProg K)) :
    ∀ (es : List Bool) (rest : List Sym) (S : K → List Sym), TermOK rest →
      S k = es.map Sym.bit ++ rest →
      Eval ρ (.loop optIsBit (dropBody k)) ⟨(es.map Sym.bit ++ rest).head?, S⟩
        ⟨rest.head?, Function.update S k rest⟩ (3 * es.length + 1)
  | [], rest, S, hrest, hS => by
    refine (Eval.loop_false (optIsBit_head?_of_termOK hrest)).of_eq ?_ rfl
    simp only [List.map_nil, List.nil_append] at hS ⊢
    rw [← hS, Function.update_eq_self]
  | e :: es, rest, S, hrest, hS => by
    have h1 : Eval ρ (.pop k fun r _ => r) ⟨((e :: es).map Sym.bit ++ rest).head?, S⟩
        ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_pop' ρ k _ _ S _ (.bit e) (es.map Sym.bit ++ rest) hS rfl
    have h2 : Eval ρ (peekR k) ⟨some (.bit e), Function.update S k (es.map Sym.bit ++ rest)⟩
        ⟨(es.map Sym.bit ++ rest).head?, Function.update S k (es.map Sym.bit ++ rest)⟩ 1 :=
      eval_peek' ρ k _ _ _ _ (by rw [Function.update_self])
    have ih := dropBits_loop_eval k ρ es rest (Function.update S k (es.map Sym.bit ++ rest)) hrest
      (Function.update_self _ _ _)
    rw [Function.update_idem] at ih
    exact (Eval.loop_true (by rfl) (Eval.seq h1 h2) ih).of_eq rfl
      (by simp only [List.length_cons]; omega)

/-- **dropBits**, exact. -/
theorem dropBits_eval (k : K) (ρ : List (SProg K)) (v : Option Sym) (es : List Bool)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S k = es.map Sym.bit ++ rest) :
    Eval ρ (dropBits k) ⟨v, S⟩ ⟨rest.head?, Function.update S k rest⟩ (3 * es.length + 2) :=
  (Eval.seq (eval_peek' ρ k (fun _ o => o) v S _ (by rw [hS]))
    (dropBits_loop_eval k ρ es rest S hrest hS)).of_eq rfl (by omega)

theorem hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    hdrSyms (f :: fs) = natSyms f ++ Sym.mark :: hdrSyms fs := by
  simp [hdrSyms, List.flatMap_cons]

theorem length_hdrSyms_cons (f : ℕ) (fs : List ℕ) :
    (hdrSyms (f :: fs)).length = bitLen f + 1 + (hdrSyms fs).length := by
  rw [hdrSyms_cons, List.length_append, List.length_cons, length_natSyms]
  omega

/-- **fetchField**: copy field `i` of the header on `src` onto `dst`; everything else restored. -/
theorem fetchField_eval {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp)
    (ρ : List (SProg K)) :
    ∀ (i : ℕ) (fs : List ℕ) (rest : List Sym) (S : K → List Sym) (v : Option Sym), i < fs.length →
      S src = hdrSyms fs ++ rest → TermOK (S tmp) →
      ∃ v' t, Eval ρ (fetchField src dst tmp i) ⟨v, S⟩
        ⟨v', Function.update S dst (natSyms (fs.getD i 0) ++ S dst)⟩ t ∧
        t ≤ 12 * (hdrSyms fs).length
  | _, [], _, _, _, hi, _, _ => by simp at hi
  | 0, f :: fs, rest, S, v, _, hS, _ => by
    have e := copyBlock_eval hsd hst hdt ρ v (encodeNat f) (Sym.mark :: (hdrSyms fs ++ rest)) S
      (TermOK.cons (by rfl) _) (by rw [hS, hdrSyms_cons, List.append_assoc]; rfl)
    refine ⟨_, _, e, ?_⟩
    rw [length_hdrSyms_cons]
    simp only [bitLen] at *
    omega
  | i + 1, f :: fs, rest, S, v, hi, hS, htmp => by
    have hS0 : S src = (encodeNat f).map Sym.bit ++ (Sym.mark :: (hdrSyms fs ++ rest)) := by
      rw [hS, hdrSyms_cons, List.append_assoc]
      rfl
    -- 1. move field `f` to `tmp`
    have e1 := moveBlock_eval hst ρ v (encodeNat f) (Sym.mark :: (hdrSyms fs ++ rest)) S
      (TermOK.cons (by rfl) _) hS0
    set S1 := Function.update (Function.update S src (Sym.mark :: (hdrSyms fs ++ rest))) tmp
      ((encodeNat f).reverse.map Sym.bit ++ S tmp) with hS1
    -- 2. move the mark
    have e2 : Eval ρ (popR src) ⟨some Sym.mark, S1⟩
        ⟨some Sym.mark, Function.update S1 src (hdrSyms fs ++ rest)⟩ 1 :=
      eval_pop' ρ src _ _ S1 _ Sym.mark (hdrSyms fs ++ rest)
        (by rw [hS1, Function.update_of_ne hst, Function.update_self]) rfl
    set S2 := Function.update S1 src (hdrSyms fs ++ rest) with hS2
    have e3 : Eval ρ (pushR tmp) ⟨some Sym.mark, S2⟩
        ⟨some Sym.mark, Function.update S2 tmp (Sym.mark :: S2 tmp)⟩ 1 :=
      (Eval.push ρ tmp (fun r => r.getD .sep) (some Sym.mark) S2).of_eq rfl rfl
    set S3 := Function.update S2 tmp (Sym.mark :: S2 tmp) with hS3
    have hS3src : S3 src = hdrSyms fs ++ rest := by
      rw [hS3, Function.update_of_ne hst, hS2, Function.update_self]
    have hS3tmp : S3 tmp = Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S tmp) := by
      rw [hS3, Function.update_self, hS2, Function.update_of_ne (Ne.symm hst), hS1,
        Function.update_self]
    have hS3dst : S3 dst = S dst := by
      rw [hS3, Function.update_of_ne hdt, hS2, Function.update_of_ne (Ne.symm hsd), hS1,
        Function.update_of_ne hdt, Function.update_of_ne (Ne.symm hsd)]
    -- 3. recursive fetch
    obtain ⟨v4, t4, e4, ht4⟩ := fetchField_eval hsd hst hdt ρ i fs rest S3 (some Sym.mark)
      (by simpa using hi) hS3src (by rw [hS3tmp]; exact TermOK.cons (by rfl) _)
    set S4 := Function.update S3 dst (natSyms (fs.getD i 0) ++ S3 dst) with hS4
    have hS4tmp : S4 tmp = Sym.mark :: ((encodeNat f).reverse.map Sym.bit ++ S tmp) := by
      rw [hS4, Function.update_of_ne (Ne.symm hdt), hS3tmp]
    -- 4. move the mark back
    have e5 : Eval ρ (popR tmp) ⟨v4, S4⟩
        ⟨some Sym.mark, Function.update S4 tmp ((encodeNat f).reverse.map Sym.bit ++ S tmp)⟩ 1 :=
      eval_pop' ρ tmp _ _ S4 _ Sym.mark _ hS4tmp rfl
    set S5 := Function.update S4 tmp ((encodeNat f).reverse.map Sym.bit ++ S tmp) with hS5
    have e6 : Eval ρ (pushR src) ⟨some Sym.mark, S5⟩
        ⟨some Sym.mark, Function.update S5 src (Sym.mark :: S5 src)⟩ 1 :=
      (Eval.push ρ src (fun r => r.getD .sep) (some Sym.mark) S5).of_eq rfl rfl
    set S6 := Function.update S5 src (Sym.mark :: S5 src) with hS6
    have hS6tmp : S6 tmp = (encodeNat f).reverse.map Sym.bit ++ S tmp := by
      rw [hS6, Function.update_of_ne (Ne.symm hst), hS5, Function.update_self]
    -- 5. move field `f` back
    have e7 := moveBlock_eval (Ne.symm hst) ρ (some Sym.mark) (encodeNat f).reverse (S tmp) S6
      htmp hS6tmp
    refine ⟨(S tmp).head?, _, (Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5
      (Eval.seq e6 e7)))))).of_eq ?_ rfl, ?_⟩
    · congr 1
      have hS5src : S5 src = hdrSyms fs ++ rest := by
        rw [hS5, Function.update_of_ne hst, hS4, Function.update_of_ne hsd, hS3src]
      funext k
      simp only [hS6, hS5, hS4, hS3dst, Function.update_apply, List.reverse_reverse,
        List.getD_cons_succ]
      split_ifs with h1 h2 h3 h4 h5 <;> subst_vars <;> simp_all [natSyms]
    · rw [length_hdrSyms_cons]
      simp only [List.length_reverse]
      simp only [bitLen] at *
      omega

end Evals

/-! ## `Runs` forms, through a register lens -/

section Steps

variable {K σ : Type} [DecidableEq K] (l : Lens σ (Option Sym))

theorem rs_push (k : K) (x : Sym) (S : K → List Sym) :
    Runs ((pushC k x).liftRegs l) S (Function.update S k (x :: S k)) (fun _ => True) 1 :=
  runs_liftMacro l (Qr := fun _ => True) fun r => ⟨r, 1, Eval.push _ _ _ _ _, trivial, le_refl _⟩

theorem rs_pop (k : K) (x : Sym) (tl : List Sym) (S : K → List Sym) (hk : S k = x :: tl) :
    Runs ((popR k).liftRegs l) S (Function.update S k tl) (fun v => l.get v = some x) 1 :=
  runs_liftMacro l (Qr := fun r => r = some x) fun r =>
    ⟨some x, 1, eval_pop' [] k (fun _ o => o) r S _ x tl hk rfl, rfl, le_refl _⟩

theorem rs_peek (k : K) (S : K → List Sym) :
    Runs ((peekR k).liftRegs l) S S (fun v => l.get v = (S k).head?) 1 :=
  runs_liftMacro l (Qr := fun r => r = (S k).head?) fun r =>
    ⟨(S k).head?, 1, eval_peek' [] k (fun _ o => o) r S _ rfl, rfl, le_refl _⟩

theorem rs_moveTo {src dst : K} (hne : src ≠ dst) (stop : Sym) (d rest : List Sym)
    (S : K → List Sym) (hd : stop ∉ d) (hS : S src = d ++ stop :: rest) :
    Runs ((moveTo stop src dst).liftRegs l) S
      (Function.update (Function.update S src rest) dst (d.reverse ++ S dst)) (fun _ => True)
      (3 * d.length + 2) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, moveTo_eval hne stop [] r d rest S hd hS, trivial, le_refl _⟩

theorem rs_moveThrough {src dst : K} (hne : src ≠ dst) (stop : Sym) (d rest : List Sym)
    (S : K → List Sym) (hd : stop ∉ d) (hS : S src = d ++ stop :: rest) :
    Runs ((moveThrough stop src dst).liftRegs l) S
      (Function.update (Function.update S src rest) dst (stop :: (d.reverse ++ S dst)))
      (fun _ => True) (3 * d.length + 3) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, moveThrough_eval hne stop [] r d rest S hd hS, trivial, le_refl _⟩

theorem rs_dropBits (k : K) (a : ℕ) (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest)
    (hS : S k = natSyms a ++ rest) :
    Runs ((dropBits k).liftRegs l) S (Function.update S k rest) (fun _ => True)
      (3 * bitLen a + 2) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, dropBits_eval k [] r (encodeNat a) rest S hrest hS, trivial, le_refl _⟩

theorem rs_copy {src dst tmp : K} (h1 : src ≠ dst) (h2 : src ≠ tmp) (h3 : dst ≠ tmp) (a : ℕ)
    (rest : List Sym) (S : K → List Sym) (hrest : TermOK rest) (hS : S src = natSyms a ++ rest) :
    Runs ((copyBlock src dst tmp).liftRegs l) S (Function.update S dst (natSyms a ++ S dst))
      (fun _ => True) (7 * bitLen a + 7) :=
  runs_liftMacro l (Qr := fun _ => True) fun r =>
    ⟨_, _, copyBlock_eval h1 h2 h3 [] r (encodeNat a) rest S hrest hS, trivial, le_refl _⟩

theorem rs_inc {k t : K} (hkt : k ≠ t) (a : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms a ++ rest) :
    Runs ((inc k t).liftRegs l) S (Function.update S k (natSyms (a + 1) ++ rest))
      (fun _ => True) (6 * bitLen a + 9) := by
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  obtain ⟨c, hc, e⟩ := inc_eval hkt [] r (encodeNat a) rest S hrest hS
  rw [← encodeNat_succ] at e
  have := ones_le_length (encodeNat a)
  exact ⟨_, c, e, trivial, by simp only [bitLen]; omega⟩

theorem rs_dec {k t : K} (hkt : k ≠ t) (a : ℕ) (rest : List Sym) (S : K → List Sym)
    (hrest : TermOK rest) (hS : S k = natSyms (a + 1) ++ rest) :
    Runs ((dec k t).liftRegs l) S (Function.update S k (natSyms a ++ rest))
      (fun _ => True) (6 * bitLen (a + 1) + 8) := by
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  have := zerosLead_le_length (encodeNat (a + 1))
  exact ⟨_, _, dec_eval hkt [] r a rest S hrest hS, trivial, by simp only [bitLen]; omega⟩

theorem rs_fetch {src dst tmp : K} (hsd : src ≠ dst) (hst : src ≠ tmp) (hdt : dst ≠ tmp) (i : ℕ)
    (fs : List ℕ) (rest : List Sym) (S : K → List Sym) (hi : i < fs.length)
    (hS : S src = hdrSyms fs ++ rest) (htmp : TermOK (S tmp)) :
    Runs ((fetchField src dst tmp i).liftRegs l) S
      (Function.update S dst (natSyms (fs.getD i 0) ++ S dst)) (fun _ => True)
      (12 * (hdrSyms fs).length) :=
  runs_liftMacro l (Qr := fun _ => True) fun r => by
    obtain ⟨v', t, e, ht⟩ := fetchField_eval hsd hst hdt [] i fs rest S r hi hS htmp
    exact ⟨v', t, e, trivial, ht⟩

theorem rs_moveRec {src dst : K} (hne : src ≠ dst) (rc rest : List Sym) (S : K → List Sym)
    (hr : RecOK rc) (hS : S src = rc ++ rest) :
    Runs ((moveRec src dst).liftRegs l) S
      (Function.update (Function.update S src rest) dst (rc.reverse ++ S dst)) (fun _ => True)
      (3 * rc.length) := by
  obtain ⟨d, rfl, hd⟩ := hr
  refine runs_liftMacro l (Qr := fun _ => True) fun r => ?_
  have e := moveRec_eval hne r d rest S hd (by rw [hS, List.append_assoc, List.singleton_append])
  refine ⟨some Sym.sep, 3 * d.length + 3, e.of_eq ?_ rfl, trivial, ?_⟩
  · simp [List.reverse_append]
  · simp only [List.length_append, List.length_singleton]
    omega

end Steps

#assert_std_axioms eval_push' eval_pop' eval_peek' moveTo_loop_eval moveTo_eval moveThrough_eval
  dropBits_loop_eval dropBits_eval hdrSyms_cons length_hdrSyms_cons fetchField_eval rs_push rs_pop
  rs_peek rs_moveTo rs_moveThrough rs_dropBits rs_copy rs_inc rs_dec rs_fetch rs_moveRec

end WP.W9e
