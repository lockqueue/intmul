import WP.W9sp.Value

/-!
# WP.W9sp.State — the host state normal form of `W9_splitPack`, and the blind transfer

The program touches eight host stacks: `S`, `C0`, `OA`, `OB` and the scratch stacks `sB` (copy of
`b`), `sN` (the counter `2^K0`), `sT` (one chunk), `sO` (the packed entries, reversed). `W.toB σ w`
is `σ` with these eight stacks replaced by the fields of `w`; `toB_*` read a field and `upd_*` turn a
host update into a field update.

`rewindTo src dst g` (copied from `WP.W9comp.Kit`) moves the symbols of `src` onto `dst` down to the
first `g`, which is popped; `HT.rewind` is its host rule.
-/

namespace WP.W9sp

open TMFw TMFw.Lib TMFw.Contracts WP.W7k2

/-- Scratch: copy of `b`. -/
abbrev sB : H := .inr 0
/-- Scratch: the loop counter. -/
abbrev sN : H := .inr 1
/-- Scratch: one chunk. -/
abbrev sT : H := .inr 2
/-- Scratch: the packed entries, reversed. -/
abbrev sO : H := .inr 3

/-- Contents of the eight working stacks. -/
structure W where
  s : List Sym
  c0 : List Sym
  oa : List Sym
  ob : List Sym
  xb : List Sym
  xn : List Sym
  xt : List Sym
  xo : List Sym

/-- `σ` with the working stacks replaced. -/
def W.toB (σ : H → List Sym) (w : W) : H → List Sym := fun k =>
  if k = hS then w.s else if k = hC0 then w.c0 else if k = hOA then w.oa else if k = hOB then w.ob
  else if k = sB then w.xb else if k = sN then w.xn else if k = sT then w.xt
  else if k = sO then w.xo else σ k

section toB

variable (σ : H → List Sym) (w : W) (v : List Sym)

@[simp] theorem toB_S : w.toB σ hS = w.s := by simp [W.toB]
@[simp] theorem toB_C0 : w.toB σ hC0 = w.c0 := by simp [W.toB]
@[simp] theorem toB_OA : w.toB σ hOA = w.oa := by simp [W.toB]
@[simp] theorem toB_OB : w.toB σ hOB = w.ob := by simp [W.toB]
@[simp] theorem toB_sB : w.toB σ sB = w.xb := by simp [W.toB]
@[simp] theorem toB_sN : w.toB σ sN = w.xn := by simp [W.toB]
@[simp] theorem toB_sT : w.toB σ sT = w.xt := by simp [W.toB]
@[simp] theorem toB_sO : w.toB σ sO = w.xo := by simp [W.toB]

theorem upd_S : Function.update (w.toB σ) hS v = { w with s := v }.toB σ := by
  funext k
  by_cases e : k = hS
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_C0 : Function.update (w.toB σ) hC0 v = { w with c0 := v }.toB σ := by
  funext k
  by_cases e : k = hC0
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_OA : Function.update (w.toB σ) hOA v = { w with oa := v }.toB σ := by
  funext k
  by_cases e : k = hOA
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_OB : Function.update (w.toB σ) hOB v = { w with ob := v }.toB σ := by
  funext k
  by_cases e : k = hOB
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_sB : Function.update (w.toB σ) sB v = { w with xb := v }.toB σ := by
  funext k
  by_cases e : k = sB
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_sN : Function.update (w.toB σ) sN v = { w with xn := v }.toB σ := by
  funext k
  by_cases e : k = sN
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_sT : Function.update (w.toB σ) sT v = { w with xt := v }.toB σ := by
  funext k
  by_cases e : k = sT
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

theorem upd_sO : Function.update (w.toB σ) sO v = { w with xo := v }.toB σ := by
  funext k
  by_cases e : k = sO
  · subst e; simp
  · rw [Function.update_of_ne e]; simp [W.toB, e]

/-- The initial state in normal form. -/
theorem toB_self : W.toB σ ⟨σ hS, σ hC0, σ hOA, σ hOB, σ sB, σ sN, σ sT, σ sO⟩ = σ := by
  funext k
  unfold W.toB
  split_ifs <;> simp_all

end toB

/-! ## Blind transfer down to a sentinel (from `WP.W9comp.Kit`) -/

/-- Loop test of `rewindTo`: the register holds a symbol other than `g`. -/
def notG (g : Sym) : Option Sym → Bool
  | some x => !(decide (x = g))
  | none => false

/-- Loop body of `rewindTo`: push the register onto `dst`, pop `src`. -/
def rewindBody {K : Type} (src dst : K) : SProg K := .seq (pushR dst) (popR src)

/-- Move symbols from `src` to `dst` down to the first `g`, which is popped and dropped. -/
def rewindTo {K : Type} (src dst : K) (g : Sym) : SProg K :=
  .seq (popR src) (.loop (notG g) (rewindBody src dst))

section Rewind

variable {K : Type} [DecidableEq K]

theorem rewind_loop_eval {src dst : K} (hne : src ≠ dst) (g : Sym) :
    ∀ (L rest : List Sym) (S : K → List Sym), g ∉ L → S src = (L ++ g :: rest).tail →
      Eval [] (.loop (notG g) (rewindBody src dst)) ⟨(L ++ g :: rest).head?, S⟩
        ⟨some g, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
        (3 * L.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by simp [notG])).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some g, S⟩ : SSt K) =
      ⟨some g, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: L, rest, S, hg, hS => by
    have hx : x ≠ g := fun h => hg (h ▸ List.mem_cons_self ..)
    have hg' : g ∉ L := fun h => hg (List.mem_cons_of_mem _ h)
    have hS' : S src = L ++ g :: rest := hS
    have hpush : Eval [] (pushR dst) ⟨some x, S⟩ ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = L ++ g :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(L ++ g :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (L ++ g :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := rewind_loop_eval hne g L rest
      (Function.update (Function.update S dst (x :: S dst)) src (L ++ g :: rest).tail) hg'
      (Function.update_self _ _ _)
    refine (Eval.loop_true (by simp [notG, hx]) (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

/-- **rewindTo**, exact. -/
theorem rewindTo_eval {src dst : K} (hne : src ≠ dst) (g : Sym) (v : Option Sym)
    (L rest : List Sym) (S : K → List Sym) (hg : g ∉ L) (hS : S src = L ++ g :: rest) :
    Eval [] (rewindTo src dst g) ⟨v, S⟩
      ⟨some g, Function.update (Function.update S src rest) dst (L.reverse ++ S dst)⟩
      (3 * L.length + 2) := by
  have h1 : Eval [] (popR src) ⟨v, S⟩
      ⟨(L ++ g :: rest).head?, Function.update S src (L ++ g :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := rewind_loop_eval hne g L rest (Function.update S src (L ++ g :: rest).tail) hg
    (Function.update_self _ _ _)
  refine (Eval.seq h1 h2).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

end Rewind

theorem rewindTo_closed {σ : Type} (l : Lens σ (Option Sym)) {a b : ℕ} (src dst : Loc a b)
    (g : Sym) : ((rewindTo src dst g).liftRegs l).Closed :=
  freeBelow_liftRegs l _ 0 (by simp [Prog.FreeBelow, rewindTo, rewindBody, pushR, popR])

/-- Host rule of the lifted `rewindTo`. -/
theorem HT.rewind {σ : Type} (l : Lens σ (Option Sym)) {a b : ℕ} {src dst : Loc a b}
    (hne : src ≠ dst) (g : Sym) (B : Loc a b → List Sym) (L rest : List Sym) (hg : g ∉ L)
    (hB : B src = L ++ g :: rest) :
    HT [] B ((rewindTo src dst g).liftRegs l)
      (Function.update (Function.update B src rest) dst (L.reverse ++ B dst)) (3 * L.length + 2) := by
  rintro ⟨v, S⟩ hS
  change S = B at hS
  subst hS
  exact ⟨_, _, Eval.liftRegs l (rewindTo_eval hne g (l.get v) L rest S hg hB) v rfl, rfl, le_rfl⟩

#assert_std_axioms toB_S toB_C0 toB_OA toB_OB toB_sB toB_sN toB_sT toB_sO upd_S upd_C0 upd_OA
  upd_OB upd_sB upd_sN upd_sT upd_sO toB_self rewind_loop_eval rewindTo_eval rewindTo_closed
  HT.rewind

end WP.W9sp
