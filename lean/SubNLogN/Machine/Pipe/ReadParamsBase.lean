import SubNLogN.Machine.Pipe.GuardBase
import SubNLogN.Machine.Pipe.BranchDefs
import SubNLogN.Machine.Pipe.ReadParamsCost

/-!
# Read-parameters kernel, part 1: unary-register calculus and arithmetic routines

Helpers (namespace `SubNLogN.Machine.Pipe.ReadParamsAux`) for
`SubNLogN.Machine.Pipe.readParams_holds_of` / `readParams_holds` (`ReadParamsMain.lean`,
`ReadParams.lean`).

* Layout: scratch stacks `RE` (persistent unary registers `B K I P0 PP Dk L Mm`, unary work
  stacks, bit buffers `H G O`); `mkS S0 u` is the state whose unary scratch stacks hold `u e`
  marks; `MS p S0 u S0' u' B` ("composite step") says that `p` takes `(S0, u)` to `(S0', u')`
  within `B` steps from any register.
* Primitive steps on unary stacks (push, pop, peek, move, copy, clear, `pushMs`, `cpN`).
* Unary arithmetic, each with its exact final state and a cost bound: multiplication `mulU`,
  comparison `leTest`, powers `powU`, the linear search `search`, integer roots
  (`rootSearch_ms`: `Y := ⌊RAD^(1/e)⌋ = floorRatPow RAD 1 e`; `iterSqrt_ms`:
  `RAD := floorRatPow RAD 1 (2^n)`), ceiling division (`divSearch_ms`) and truncated
  subtraction (`subU_ms`).
-/

namespace SubNLogN.Machine.Pipe.ReadParamsAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Machine.Pipe.GuardAux

/-- Scratch stacks of the read-parameters kernel: persistent unary registers
`B K I P0 PP Dk L Mm`, unary work stacks, and the bit buffers `H G O`. -/
inductive RE
  | B | K | I | P0 | PP | Dk | L | Mm
  | T | NUM | MA | MB | MZ | MB2 | CA | CB | Y | RAD | BASE | Q | CNT | X | PAR | V | Z
  | H | G | O
  deriving DecidableEq

/-- All scratch stacks. -/
def RE.all : List RE :=
  [.B, .K, .I, .P0, .PP, .Dk, .L, .Mm, .T, .NUM, .MA, .MB, .MZ, .MB2, .CA, .CB, .Y, .RAD, .BASE,
    .Q, .CNT, .X, .PAR, .V, .Z, .H, .G, .O]

instance : Fintype RE where
  elems := ⟨RE.all, Multiset.coe_nodup.2 (by decide)⟩
  complete := fun x => by
    rw [Finset.mem_mk, Multiset.mem_coe]
    cases x <;> simp [RE.all]

/-- Stack indices of the kernel. -/
abbrev RK : Type := KLoc PN RE

/-- Unary scratch stacks (all except the bit buffers `H`, `G`, `O`). -/
def isU : RE → Bool
  | .H => false
  | .G => false
  | .O => false
  | _ => true

/-- The state whose unary scratch stacks hold `u e` marks; the named stacks and the bit buffers
are read from `S0`. -/
def mkS (S0 : RK → List Sym) (u : RE → ℕ) : RK → List Sym
  | .inl n => S0 (.inl n)
  | .inr e => if isU e then List.replicate (u e) .mark else S0 (.inr e)

@[simp] theorem mkS_inl (S0 : RK → List Sym) (u : RE → ℕ) (n : PN) :
    mkS S0 u (.inl n) = S0 (.inl n) := rfl

theorem mkS_U {e : RE} (h : isU e = true) (S0 : RK → List Sym) (u : RE → ℕ) :
    mkS S0 u (.inr e) = List.replicate (u e) .mark := by
  simp [mkS, h]

theorem mkS_N {e : RE} (h : isU e = false) (S0 : RK → List Sym) (u : RE → ℕ) :
    mkS S0 u (.inr e) = S0 (.inr e) := by
  simp [mkS, h]

theorem upd_mkS_U {e : RE} (h : isU e = true) (S0 : RK → List Sym) (u : RE → ℕ) (n : ℕ) :
    Function.update (mkS S0 u) (.inr e) (List.replicate n .mark) =
      mkS S0 (Function.update u e n) := by
  funext k
  rcases k with a | e'
  · simp [mkS, Function.update_apply]
  · by_cases he : e' = e
    · subst he; simp [mkS, h]
    · simp [mkS, Function.update_apply, he]

theorem upd_mkS_inl (S0 : RK → List Sym) (u : RE → ℕ) (n : PN) (l : List Sym) :
    Function.update (mkS S0 u) (.inl n) l = mkS (Function.update S0 (.inl n) l) u := by
  funext k
  rcases k with a | e
  · by_cases ha : a = n
    · subst ha; simp
    · simp [Function.update_apply, ha]
  · simp [mkS, Function.update_apply]

theorem upd_mkS_N {e : RE} (h : isU e = false) (S0 : RK → List Sym) (u : RE → ℕ)
    (l : List Sym) :
    Function.update (mkS S0 u) (.inr e) l = mkS (Function.update S0 (.inr e) l) u := by
  funext k
  rcases k with a | e'
  · simp [mkS, Function.update_apply]
  · by_cases he : e' = e
    · subst he; simp [mkS, h]
    · simp [mkS, Function.update_apply, he]

/-- A clean kernel state is the unary state with all counters `0`. -/
theorem mkS_clean (S : RK → List Sym) (hcl : KClean S) : mkS S (fun _ => 0) = S := by
  funext k
  rcases k with a | e
  · rfl
  · have h0 := hcl e
    simp only [mkS, List.replicate_zero]
    split_ifs
    · exact h0.symm
    · rfl

/-! ## Composite steps -/

/-- **Composite step**: from the unary state `(S0, u)` and any register, `p` reaches the unary state
`(S0', u')` within `B` steps. -/
def MS (p : SProg RK) (S0 : RK → List Sym) (u : RE → ℕ) (S0' : RK → List Sym) (u' : RE → ℕ)
    (B : ℕ) : Prop :=
  ∀ v, ∃ r t, t ≤ B ∧ Eval [] p ⟨v, mkS S0 u⟩ ⟨r, mkS S0' u'⟩ t

theorem MS.seq {p q : SProg RK} {S0 S1 S2 : RK → List Sym} {u0 u1 u2 : RE → ℕ} {B1 B2 : ℕ}
    (h1 : MS p S0 u0 S1 u1 B1) (h2 : MS q S1 u1 S2 u2 B2) :
    MS (.seq p q) S0 u0 S2 u2 (B1 + B2) := by
  intro v
  obtain ⟨r1, t1, ht1, e1⟩ := h1 v
  obtain ⟨r2, t2, ht2, e2⟩ := h2 r1
  exact ⟨r2, t1 + t2, by omega, Eval.seq e1 e2⟩

theorem MS.mono {p : SProg RK} {S0 S0' : RK → List Sym} {u u' : RE → ℕ} {B B' : ℕ}
    (h : MS p S0 u S0' u' B) (hB : B ≤ B') : MS p S0 u S0' u' B' := by
  intro v
  obtain ⟨r, t, ht, e⟩ := h v
  exact ⟨r, t, by omega, e⟩

theorem MS.of_eq {p : SProg RK} {S0 S0' S0'' : RK → List Sym} {u u' u'' : RE → ℕ} {B : ℕ}
    (h : MS p S0 u S0' u' B) (hS : S0' = S0'') (hu : u' = u'') : MS p S0 u S0'' u'' B := by
  subst hS hu; exact h

theorem MS.of_eval {p : SProg RK} {S0 S0' : RK → List Sym} {u u' : RE → ℕ} {t : ℕ}
    (h : ∀ v, ∃ r, Eval [] p ⟨v, mkS S0 u⟩ ⟨r, mkS S0' u'⟩ t) : MS p S0 u S0' u' t := by
  intro v
  obtain ⟨r, e⟩ := h v
  exact ⟨r, t, le_rfl, e⟩

theorem MS.skip (S0 : RK → List Sym) (u : RE → ℕ) : MS skip S0 u S0 u 1 :=
  MS.of_eval fun v => ⟨v, skip_eval [] _⟩

/-! ## Primitive steps on unary stacks -/

theorem hd_rep (n : ℕ) :
    (List.replicate n Sym.mark).head? = if n = 0 then none else some Sym.mark := by
  cases n <;> rfl

theorem isSomeB_hd (n : ℕ) : isSomeB (List.replicate n Sym.mark).head? = decide (n ≠ 0) := by
  cases n <;> rfl

theorem peekU_eval {a : RE} (ha : isU a = true) (v : Option Sym) (S0 : RK → List Sym)
    (u : RE → ℕ) :
    Eval [] (peekR (.inr a)) ⟨v, mkS S0 u⟩ ⟨(List.replicate (u a) Sym.mark).head?, mkS S0 u⟩ 1 := by
  refine (Eval.peek [] (.inr a) (fun _ o => o) v (mkS S0 u)).of_eq ?_ rfl
  rw [mkS_U ha]

theorem popU_eval {a : RE} (ha : isU a = true) (v : Option Sym) (S0 : RK → List Sym)
    (u : RE → ℕ) :
    Eval [] (popR (.inr a)) ⟨v, mkS S0 u⟩
      ⟨(List.replicate (u a) Sym.mark).head?, mkS S0 (Function.update u a (u a - 1))⟩ 1 := by
  refine (Eval.pop [] (.inr a) (fun _ o => o) v (mkS S0 u)).of_eq ?_ rfl
  rw [mkS_U ha, List.tail_replicate, upd_mkS_U ha]

theorem pushU_eval {a : RE} (ha : isU a = true) (v : Option Sym) (S0 : RK → List Sym)
    (u : RE → ℕ) :
    Eval [] (pushC (.inr a) .mark) ⟨v, mkS S0 u⟩
      ⟨v, mkS S0 (Function.update u a (u a + 1))⟩ 1 := by
  have e := Eval.push [] (.inr a) (fun _ => Sym.mark) v (mkS S0 u)
  refine e.of_eq ?_ rfl
  rw [mkS_U ha, ← List.replicate_succ, upd_mkS_U ha]

theorem mvU_eval {a b : RE} (ha : isU a = true) (hb : isU b = true) (hab : a ≠ b)
    (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (moveAll (.inr a) (.inr b)) ⟨v, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update (Function.update u a 0) b (u a + u b))⟩ (4 * u a + 2) := by
  have hne : (Sum.inr a : RK) ≠ Sum.inr b := fun h => hab (Sum.inr_injective h)
  have e := moveAll_eval hne [] v _ (mkS S0 u) (mkS_U ha S0 u)
  rw [List.length_replicate, List.reverse_replicate, mkS_U hb, List.replicate_append_replicate,
    show ([] : List Sym) = List.replicate 0 Sym.mark from rfl, upd_mkS_U ha, upd_mkS_U hb] at e
  exact e

theorem cpU_eval {a b t : RE} (ha : isU a = true) (hb : isU b = true) (ht : isU t = true)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (v : Option Sym) (S0 : RK → List Sym)
    (u : RE → ℕ) (hu : u t = 0) :
    Eval [] (copyAll (.inr a) (.inr b) (.inr t)) ⟨v, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update u b (u a + u b))⟩ (9 * u a + 4) := by
  have e := copyAll_eval (src := (.inr a : RK)) (dst := .inr b) (tmp := .inr t)
    (fun h => hab (Sum.inr_injective h)) (fun h => hat (Sum.inr_injective h))
    (fun h => hbt (Sum.inr_injective h)) [] v _ (mkS S0 u) (mkS_U ha S0 u)
    (by rw [mkS_U ht, hu]; rfl)
  rw [List.length_replicate, List.reverse_replicate, mkS_U hb, List.replicate_append_replicate,
    upd_mkS_U hb] at e
  exact e

theorem clrU_eval {a : RE} (ha : isU a = true) (v : Option Sym) (S0 : RK → List Sym)
    (u : RE → ℕ) :
    Eval [] (clearM (.inr a)) ⟨v, mkS S0 u⟩ ⟨none, mkS S0 (Function.update u a 0)⟩
      (3 * u a + 2) := by
  have e := clearM_eval (k := (.inr a : RK)) [] v _ (mkS S0 u) (mkS_U ha S0 u)
  rw [List.length_replicate, show ([] : List Sym) = List.replicate 0 Sym.mark from rfl,
    upd_mkS_U ha] at e
  exact e

theorem push_ms {a : RE} (ha : isU a = true) (S0 : RK → List Sym) (u : RE → ℕ) :
    MS (pushC (.inr a) .mark) S0 u S0 (Function.update u a (u a + 1)) 1 :=
  MS.of_eval fun v => ⟨v, pushU_eval ha v S0 u⟩

theorem pop_ms {a : RE} (ha : isU a = true) (S0 : RK → List Sym) (u : RE → ℕ) :
    MS (popR (.inr a)) S0 u S0 (Function.update u a (u a - 1)) 1 :=
  MS.of_eval fun v => ⟨_, popU_eval ha v S0 u⟩

theorem mv_ms {a b : RE} (ha : isU a = true) (hb : isU b = true) (hab : a ≠ b)
    (S0 : RK → List Sym) (u : RE → ℕ) :
    MS (moveAll (.inr a) (.inr b)) S0 u S0
      (Function.update (Function.update u a 0) b (u a + u b)) (4 * u a + 2) :=
  MS.of_eval fun v => ⟨none, mvU_eval ha hb hab v S0 u⟩

theorem cp_ms {a b t : RE} (ha : isU a = true) (hb : isU b = true) (ht : isU t = true)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (S0 : RK → List Sym) (u : RE → ℕ) (hu : u t = 0) :
    MS (copyAll (.inr a) (.inr b) (.inr t)) S0 u S0 (Function.update u b (u a + u b))
      (9 * u a + 4) :=
  MS.of_eval fun v => ⟨none, cpU_eval ha hb ht hab hat hbt v S0 u hu⟩

theorem clr_ms {a : RE} (ha : isU a = true) (S0 : RK → List Sym) (u : RE → ℕ) :
    MS (clearM (.inr a)) S0 u S0 (Function.update u a 0) (3 * u a + 2) :=
  MS.of_eval fun v => ⟨none, clrU_eval ha v S0 u⟩

/-- Push `n` marks on `a`. -/
def pushMs (a : RE) : ℕ → SProg RK
  | 0 => skip
  | n + 1 => .seq (pushC (.inr a) .mark) (pushMs a n)

theorem pushMs_ms {a : RE} (ha : isU a = true) (S0 : RK → List Sym) :
    ∀ (n : ℕ) (u : RE → ℕ), MS (pushMs a n) S0 u S0 (Function.update u a (u a + n)) (n + 1)
  | 0, u => by
    refine ((MS.skip S0 u).of_eq rfl ?_).mono (by simp)
    simp
  | n + 1, u => by
    have h := (push_ms ha S0 u).seq (pushMs_ms ha S0 n (Function.update u a (u a + 1)))
    refine (h.mono (by omega)).of_eq rfl ?_
    rw [Function.update_self, Function.update_idem, show u a + 1 + n = u a + (n + 1) by omega]

/-- Copy `a` onto `b` `n` times (through `t`). -/
def cpN (a b t : RE) : ℕ → SProg RK
  | 0 => skip
  | n + 1 => .seq (copyAll (.inr a) (.inr b) (.inr t)) (cpN a b t n)

theorem cpN_ms {a b t : RE} (ha : isU a = true) (hb : isU b = true) (ht : isU t = true)
    (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (S0 : RK → List Sym) :
    ∀ (n : ℕ) (u : RE → ℕ), u t = 0 →
      MS (cpN a b t n) S0 u S0 (Function.update u b (u b + n * u a)) (n * (9 * u a + 4) + 1)
  | 0, u, _ => by
    refine ((MS.skip S0 u).of_eq rfl ?_).mono (by simp)
    simp
  | n + 1, u, hu => by
    have h1 := cp_ms ha hb ht hab hat hbt S0 u hu
    have h2 := cpN_ms ha hb ht hab hat hbt S0 n (Function.update u b (u a + u b))
      (by rw [Function.update_of_ne (Ne.symm hbt)]; exact hu)
    have h := h1.seq h2
    rw [Function.update_of_ne hab, Function.update_self, Function.update_idem] at h
    refine (h.mono (le_of_eq (by ring))).of_eq rfl ?_
    congr 1
    ring

/-! ## Unary multiplication `MZ += MA · MB` -/

/-- Loop body of `mulU`. -/
def mulBody : SProg RK :=
  .seq (.seq (.seq (popR (.inr .MB)) (pushC (.inr .MB2) .mark))
    (copyAll (.inr .MA) (.inr .MZ) (.inr .T))) (peekR (.inr .MB))

/-- `MZ += MA · MB`; `MA`, `MB` restored (through `MB2`, `T`). -/
def mulU : SProg RK :=
  .seq (.seq (peekR (.inr .MB)) (.loop isSomeB mulBody)) (moveAll (.inr .MB2) (.inr .MB))

theorem mulU_loop (S0 : RK → List Sym) : ∀ (k : ℕ) (u : RE → ℕ), u .MB = k → u .T = 0 →
    Eval [] (.loop isSomeB mulBody) ⟨(List.replicate k Sym.mark).head?, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update (Function.update (Function.update u .MB 0) .MB2
        (u .MB2 + k)) .MZ (u .MZ + k * u .MA))⟩ (k * (9 * u .MA + 8) + 1)
  | 0, u, hk, _ => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by ring)
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    congr 2
    funext e
    cases e <;> simp [hk]
  | k + 1, u, hk, hT => by
    have e1 := popU_eval (a := .MB) rfl (List.replicate (k + 1) Sym.mark).head? S0 u
    have e2 := pushU_eval (a := .MB2) rfl (List.replicate (u .MB) Sym.mark).head? S0
      (Function.update u .MB (u .MB - 1))
    set u2 := Function.update (Function.update u .MB (u .MB - 1)) .MB2
      ((Function.update u .MB (u .MB - 1)) .MB2 + 1) with hu2
    have e3 := cpU_eval (a := .MA) (b := .MZ) (t := .T) rfl rfl rfl (by decide) (by decide)
      (by decide) (List.replicate (u .MB) Sym.mark).head? S0 u2 (by simp [hu2, hT])
    set u3 := Function.update u2 .MZ (u2 .MA + u2 .MZ) with hu3
    have e4 := peekU_eval (a := .MB) rfl none S0 u3
    have h3B : u3 .MB = k := by simp [hu3, hu2, hk]
    rw [h3B] at e4
    have ih := mulU_loop S0 k u3 h3B (by simp [hu3, hu2, hT])
    have h2A : u2 .MA = u .MA := by simp [hu2]
    have h3A : u3 .MA = u .MA := by simp [hu3, hu2]
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq (Eval.seq e1 e2) e3) e4) ih).of_eq ?_ ?_
    · congr 2
      funext e
      cases e <;> simp [hu3, hu2, hk] <;> ring
    · rw [h2A, h3A]; ring

theorem mulU_ms (S0 : RK → List Sym) (u : RE → ℕ) (hT : u .T = 0) (hB2 : u .MB2 = 0) :
    MS mulU S0 u S0 (Function.update u .MZ (u .MZ + u .MB * u .MA))
      (u .MB * (9 * u .MA + 12) + 4) := by
  refine MS.of_eval fun v => ⟨none, ?_⟩
  have e0 := peekU_eval (a := .MB) rfl v S0 u
  have e1 := mulU_loop S0 (u .MB) u rfl hT
  set u1 := Function.update (Function.update (Function.update u .MB 0) .MB2 (u .MB2 + u .MB))
    .MZ (u .MZ + u .MB * u .MA) with hu1
  have e2 := mvU_eval (a := .MB2) (b := .MB) rfl rfl (by decide) none S0 u1
  have h1 : u1 .MB2 = u .MB := by simp [hu1, hB2]
  refine (Eval.seq (Eval.seq e0 e1) e2).of_eq ?_ ?_
  · congr 2
    funext e
    cases e <;> simp [hu1, hB2]
  · rw [h1]; ring

/-! ## Unary comparison -/

/-- Register `some` iff both `CA` and `CB` are nonempty. -/
def condAB : SProg RK := .seq (peekR (.inr .CA)) (.ite isSomeB (peekR (.inr .CB)) skip)

theorem condAB_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] condAB ⟨v, mkS S0 u⟩
      ⟨(List.replicate (min (u .CA) (u .CB)) Sym.mark).head?, mkS S0 u⟩ 3 := by
  have e0 := peekU_eval (a := .CA) rfl v S0 u
  rcases Nat.eq_zero_or_pos (u .CA) with h | h
  · have e1 : Eval [] (.ite isSomeB (peekR (.inr .CB)) skip)
        ⟨(List.replicate (u .CA) Sym.mark).head?, mkS S0 u⟩
        ⟨(List.replicate (u .CA) Sym.mark).head?, mkS S0 u⟩ 2 :=
      Eval.ite_false (by rw [h]; rfl) (skip_eval [] _)
    refine (Eval.seq e0 e1).of_eq ?_ rfl
    rw [h, Nat.zero_min]
  · obtain ⟨j, hj⟩ : ∃ j, u .CA = j + 1 := ⟨u .CA - 1, by omega⟩
    have e1 := Eval.ite_true (q := skip) (c := isSomeB)
      (s := ⟨(List.replicate (u .CA) Sym.mark).head?, mkS S0 u⟩) (by rw [hj]; rfl)
      (peekU_eval (a := .CB) rfl _ S0 u)
    refine (Eval.seq e0 e1).of_eq ?_ rfl
    congr 1
    rw [hd_rep, hd_rep]
    split_ifs <;> first | rfl | omega

/-- Loop body of the lock-step comparison. -/
def lockBody : SProg RK := .seq (.seq (popR (.inr .CA)) (popR (.inr .CB))) condAB

theorem lock_loop (S0 : RK → List Sym) : ∀ (m : ℕ) (u : RE → ℕ), min (u .CA) (u .CB) = m →
    Eval [] (.loop isSomeB lockBody) ⟨(List.replicate m Sym.mark).head?, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update (Function.update u .CA (u .CA - m)) .CB (u .CB - m))⟩
      (6 * m + 1)
  | 0, u, _ => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by ring)
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    simp
  | m + 1, u, hm => by
    have e1 := popU_eval (a := .CA) rfl (List.replicate (m + 1) Sym.mark).head? S0 u
    have e2 := popU_eval (a := .CB) rfl (List.replicate (u .CA) Sym.mark).head? S0
      (Function.update u .CA (u .CA - 1))
    set u2 := Function.update (Function.update u .CA (u .CA - 1)) .CB
      ((Function.update u .CA (u .CA - 1)) .CB - 1) with hu2
    have e3 := condAB_eval (List.replicate ((Function.update u .CA (u .CA - 1)) .CB) Sym.mark).head?
      S0 u2
    have hA : u2 .CA = u .CA - 1 := by simp [hu2]
    have hB : u2 .CB = u .CB - 1 := by simp [hu2]
    have hm2 : min (u2 .CA) (u2 .CB) = m := by rw [hA, hB]; omega
    rw [hm2] at e3
    have ih := lock_loop S0 m u2 hm2
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) e3) ih).of_eq ?_ (by ring)
    congr 2
    funext e
    cases e <;> simp [hu2] <;> omega

/-- **Comparison** `|CA| ≤ |CB|` (register `some` iff true); `CA`, `CB` are emptied. -/
def leTest : SProg RK :=
  .seq (.seq (.seq (.seq condAB (.loop isSomeB lockBody)) (clearM (.inr .CB)))
    (peekR (.inr .CA))) (.ite isSomeB (clearM (.inr .CA)) (.load fun _ => some .mark))

theorem leTest_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    ∃ t, t ≤ 6 * (u .CA + u .CB) + 12 ∧ Eval [] leTest ⟨v, mkS S0 u⟩
      ⟨if u .CA ≤ u .CB then some .mark else none,
        mkS S0 (Function.update (Function.update u .CA 0) .CB 0)⟩ t := by
  have e0 := condAB_eval v S0 u
  have e1 := lock_loop S0 _ u rfl
  set m := min (u .CA) (u .CB) with hm
  set u1 := Function.update (Function.update u .CA (u .CA - m)) .CB (u .CB - m) with hu1
  have e2 := clrU_eval (a := .CB) rfl none S0 u1
  set u2 := Function.update u1 .CB 0 with hu2
  have e3 := peekU_eval (a := .CA) rfl none S0 u2
  have h2A : u2 .CA = u .CA - m := by simp [hu2, hu1]
  have h1B : u1 .CB = u .CB - m := by simp [hu1]
  by_cases hle : u .CA ≤ u .CB
  · have h0 : u2 .CA = 0 := by rw [h2A]; omega
    rw [h0] at e3
    have e4 : Eval [] (.ite isSomeB (clearM (.inr .CA)) (.load fun _ => some .mark))
        ⟨(List.replicate 0 Sym.mark).head?, mkS S0 u2⟩ ⟨some .mark, mkS S0 u2⟩ 2 :=
      Eval.ite_false (by rfl) (Eval.load [] _ _ _)
    refine ⟨_, ?_, (Eval.seq (Eval.seq (Eval.seq (Eval.seq e0 e1) e2) e3) e4).of_eq ?_ rfl⟩
    · rw [h1B]; omega
    · rw [if_pos hle]
      congr 2
      funext e
      cases e <;> simp [hu2, hu1] <;> omega
  · obtain ⟨j, hj⟩ : ∃ j, u2 .CA = j + 1 := ⟨u2 .CA - 1, by rw [h2A]; omega⟩
    rw [hj] at e3
    have e4 := Eval.ite_true (q := (.load fun _ => some .mark : SProg RK)) (c := isSomeB)
      (s := ⟨(List.replicate (j + 1) Sym.mark).head?, mkS S0 u2⟩) (by rfl)
      (clrU_eval (a := .CA) rfl _ S0 u2)
    refine ⟨_, ?_, (Eval.seq (Eval.seq (Eval.seq (Eval.seq e0 e1) e2) e3) e4).of_eq ?_ rfl⟩
    · rw [h1B, hj]; omega
    · rw [if_neg hle]
      congr 2
      funext e
      cases e <;> simp [hu2, hu1]

/-! ## Powers `Q := BASE ^ e` -/

/-- One multiplication step `Q := Q · BASE`. -/
def powStep : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (moveAll (.inr .Q) (.inr .MA))
    (copyAll (.inr .BASE) (.inr .MB) (.inr .T))) mulU) (clearM (.inr .MA))) (clearM (.inr .MB)))
    (moveAll (.inr .MZ) (.inr .Q))

/-- `Q := BASE ^ e` (from `Q = 0`). -/
def powU : ℕ → SProg RK
  | 0 => pushC (.inr .Q) .mark
  | e + 1 => .seq (powU e) powStep

/-- The work stacks of `mulU`/`powU` are empty. -/
def PowClean (u : RE → ℕ) : Prop :=
  u .MA = 0 ∧ u .MB = 0 ∧ u .MZ = 0 ∧ u .MB2 = 0 ∧ u .T = 0

theorem powStep_ms (S0 : RK → List Sym) (u : RE → ℕ) (hc : PowClean u) :
    MS powStep S0 u S0 (Function.update u .Q (u .Q * u .BASE))
      (24 * (u .Q + 1) * (u .BASE + 1)) := by
  obtain ⟨hA, hB, hZ, hB2, hT⟩ := hc
  have h := (((((mv_ms (a := .Q) (b := .MA) rfl rfl (by decide) S0 u).seq
    (cp_ms (a := .BASE) (b := .MB) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide)
      S0 _ (by simp [hT]))).seq (mulU_ms S0 _ (by simp [hT]) (by simp [hB2]))).seq
    (clr_ms (a := .MA) rfl S0 _)).seq (clr_ms (a := .MB) rfl S0 _)).seq
    (mv_ms (a := .MZ) (b := .Q) rfl rfl (by decide) S0 _)
  refine (h.mono ?_).of_eq rfl ?_
  · simp [hA, hB, hZ]
    nlinarith [Nat.zero_le (u .Q * u .BASE)]
  · funext e
    cases e <;> simp [hA, hB, hZ] <;> ring

theorem powU_ms (S0 : RK → List Sym) : ∀ (e : ℕ) (u : RE → ℕ), PowClean u → u .Q = 0 →
    1 ≤ u .BASE → MS (powU e) S0 u S0 (Function.update u .Q (u .BASE ^ e))
      (1 + e * (24 * (u .BASE ^ e + 1) * (u .BASE + 1)))
  | 0, u, _, hQ, _ => ((push_ms (a := .Q) rfl S0 u).of_eq rfl (by rw [hQ]; simp)).mono (by simp)
  | e + 1, u, hc, hQ, hp => by
    have h1 := powU_ms S0 e u hc hQ hp
    obtain ⟨hA, hB, hZ, hB2, hT⟩ := hc
    have h2 := powStep_ms S0 (Function.update u .Q (u .BASE ^ e))
      ⟨by simp [hA], by simp [hB], by simp [hZ], by simp [hB2], by simp [hT]⟩
    have h := h1.seq h2
    simp only [Function.update_self, Function.update_idem,
      Function.update_of_ne (show RE.BASE ≠ RE.Q by decide)] at h
    have hpp : u .BASE ^ e ≤ u .BASE ^ (e + 1) := Nat.pow_le_pow_right hp (Nat.le_succ e)
    refine (h.mono ?_).of_eq rfl ?_
    · nlinarith [Nat.mul_le_mul_left ((e + 1) * (u .BASE + 1)) hpp]
    · rw [pow_succ]

/-! ## Root test, search loop -/

/-- Work stacks of the arithmetic routines. -/
def isW : RE → Bool
  | .MA | .MB | .MZ | .MB2 | .T | .Q | .BASE | .CA | .CB => true
  | _ => false

/-- The work stacks of the arithmetic routines are empty. -/
def ArClean (u : RE → ℕ) : Prop := ∀ e, isW e = true → u e = 0

theorem ArClean.upd {u : RE → ℕ} (hc : ArClean u) {e' : RE} (he' : isW e' = false) (x : ℕ) :
    ArClean (Function.update u e' x) := by
  intro e he
  have hne : e ≠ e' := by
    rintro rfl
    rw [he] at he'
    exact Bool.noConfusion he'
  rw [Function.update_of_ne hne]
  exact hc e he

theorem ArClean.pow {u : RE → ℕ} (hc : ArClean u) : PowClean u :=
  ⟨hc _ rfl, hc _ rfl, hc _ rfl, hc _ rfl, hc _ rfl⟩

/-- Straight-line part of `testRoot`: `CA := (Y + 1) ^ e`, `CB := RAD`. -/
def rootPre (e : ℕ) : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (copyAll (.inr .Y) (.inr .BASE) (.inr .T))
    (pushC (.inr .BASE) .mark)) (powU e)) (clearM (.inr .BASE))) (moveAll (.inr .Q) (.inr .CA)))
    (copyAll (.inr .RAD) (.inr .CB) (.inr .T))

/-- Test `(Y + 1) ^ e ≤ RAD` (register `some` iff true); everything restored. -/
def testRoot (e : ℕ) : SProg RK := .seq (rootPre e) leTest

theorem rootPre_ms (e : ℕ) (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u) :
    MS (rootPre e) S0 u S0
      (Function.update (Function.update u .CA ((u .Y + 1) ^ e)) .CB (u .RAD))
      ((24 * e + 30) * ((u .Y + 1) ^ e + 1) * (u .Y + 2) + 9 * u .RAD) := by
  have hT : u .T = 0 := hc _ rfl
  have hQ : u .Q = 0 := hc _ rfl
  have hBa : u .BASE = 0 := hc _ rfl
  have hCA : u .CA = 0 := hc _ rfl
  have hCB : u .CB = 0 := hc _ rfl
  have hA : u .MA = 0 := hc _ rfl
  have hB : u .MB = 0 := hc _ rfl
  have hZ : u .MZ = 0 := hc _ rfl
  have hB2 : u .MB2 = 0 := hc _ rfl
  have h := (((((cp_ms (a := .Y) (b := .BASE) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 u hT).seq (push_ms (a := .BASE) rfl S0 _)).seq
    (powU_ms S0 e _ ⟨by simp [hA], by simp [hB], by simp [hZ], by simp [hB2], by simp [hT]⟩
      (by simp [hQ]) (by simp))).seq (clr_ms (a := .BASE) rfl S0 _)).seq
    (mv_ms (a := .Q) (b := .CA) rfl rfl (by decide) S0 _)).seq
    (cp_ms (a := .RAD) (b := .CB) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide)
      S0 _ (by simp [hT]))
  refine (h.mono ?_).of_eq rfl ?_
  · simp only [Function.update_self, Function.update_idem, Function.update_of_ne,
      ne_eq, reduceCtorEq, not_false_eq_true, hBa, hCA, hCB, hQ, Nat.add_zero]
    nlinarith [Nat.zero_le ((u .Y + 1) ^ e * u .Y), Nat.one_le_pow e (u .Y + 1) (by omega)]
  · funext x
    cases x <;> simp [hQ, hBa, hCA, hCB]

/-- Cost bound of one `testRoot e` at `Y = y`, `RAD = x`. -/
def rootB (e y x : ℕ) : ℕ := (24 * e + 30) * ((y + 1) ^ e + 1) * (y + 2) + 15 * x + 6 * (y + 1) ^ e + 12

theorem rootB_mono (e x : ℕ) {y y' : ℕ} (h : y ≤ y') : rootB e y x ≤ rootB e y' x := by
  unfold rootB
  gcongr

theorem testRoot_eval (e : ℕ) (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u)
    (v : Option Sym) :
    ∃ t, t ≤ rootB e (u .Y) (u .RAD) ∧ Eval [] (testRoot e) ⟨v, mkS S0 u⟩
      ⟨if (u .Y + 1) ^ e ≤ u .RAD then some .mark else none, mkS S0 u⟩ t := by
  have hCA : u .CA = 0 := hc _ rfl
  have hCB : u .CB = 0 := hc _ rfl
  obtain ⟨r, t1, ht1, e1⟩ := rootPre_ms e S0 u hc v
  obtain ⟨t2, ht2, e2⟩ := leTest_eval r S0
    (Function.update (Function.update u .CA ((u .Y + 1) ^ e)) .CB (u .RAD))
  refine ⟨t1 + t2, ?_, (Eval.seq e1 e2).of_eq ?_ rfl⟩
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at ht2
    unfold rootB
    omega
  · have hu : Function.update (Function.update (Function.update (Function.update u .CA
        ((u .Y + 1) ^ e)) .CB (u .RAD)) .CA 0) .CB 0 = u := by
      funext x
      cases x <;> simp [hCA, hCB]
    rw [hu]
    simp

/-- Linear search: `Y` counts up while the test succeeds. -/
def search (test : SProg RK) : SProg RK :=
  .seq test (.loop isSomeB (.seq (pushC (.inr .Y) .mark) test))

theorem search_loop (test : SProg RK) (P : ℕ → Prop) [DecidablePred P] (S0 : RK → List Sym)
    (u : RE → ℕ) (ys Bt : ℕ)
    (htest : ∀ y, y ≤ ys → ∀ v, ∃ t, t ≤ Bt ∧ Eval [] test
      ⟨v, mkS S0 (Function.update u .Y y)⟩
      ⟨if P y then some .mark else none, mkS S0 (Function.update u .Y y)⟩ t)
    (hlt : ∀ y, y < ys → P y) (hys : ¬ P ys) :
    ∀ n j, j + n = ys → ∃ t, t ≤ n * (Bt + 2) + 1 ∧
      Eval [] (.loop isSomeB (.seq (pushC (.inr .Y) .mark) test))
        ⟨if P j then some .mark else none, mkS S0 (Function.update u .Y j)⟩
        ⟨none, mkS S0 (Function.update u .Y ys)⟩ t
  | 0, j, hj => by
    have hj' : j = ys := by omega
    subst hj'
    refine ⟨1, by omega, ?_⟩
    rw [if_neg hys]
    exact Eval.loop_false rfl
  | n + 1, j, hj => by
    have hPj : P j := hlt j (by omega)
    have e1 := pushU_eval (a := .Y) rfl (if P j then some .mark else none) S0
      (Function.update u .Y j)
    rw [Function.update_self, Function.update_idem] at e1
    obtain ⟨t2, ht2, e2⟩ := htest (j + 1) (by omega) (if P j then some .mark else none)
    obtain ⟨t3, ht3, e3⟩ := search_loop test P S0 u ys Bt htest hlt hys n (j + 1) (by omega)
    refine ⟨_, ?_, Eval.loop_true (by rw [if_pos hPj]; rfl) (Eval.seq e1 e2) e3⟩
    nlinarith

theorem search_ms (test : SProg RK) (P : ℕ → Prop) [DecidablePred P] (S0 : RK → List Sym)
    (u : RE → ℕ) (ys Bt : ℕ) (hY : u .Y = 0)
    (htest : ∀ y, y ≤ ys → ∀ v, ∃ t, t ≤ Bt ∧ Eval [] test
      ⟨v, mkS S0 (Function.update u .Y y)⟩
      ⟨if P y then some .mark else none, mkS S0 (Function.update u .Y y)⟩ t)
    (hlt : ∀ y, y < ys → P y) (hys : ¬ P ys) :
    MS (search test) S0 u S0 (Function.update u .Y ys) ((ys + 1) * (Bt + 2) + 1) := by
  intro v
  have hu : Function.update u .Y 0 = u := by rw [← hY, Function.update_eq_self]
  obtain ⟨t1, ht1, e1⟩ := htest 0 (Nat.zero_le _) v
  rw [hu] at e1
  obtain ⟨t2, ht2, e2⟩ := search_loop test P S0 u ys Bt htest hlt hys ys 0 (by omega)
  rw [hu] at e2
  exact ⟨none, t1 + t2, by nlinarith, Eval.seq e1 e2⟩

/-! ## Integer roots `Y := ⌊RAD ^ (1/e)⌋` -/

open SubNLogN.Math.Cost in
theorem frp_one_one (x : ℕ) : floorRatPow x 1 1 = x := by
  have key : ∀ y, y ≤ floorRatPow x 1 1 ↔ y ≤ x := by
    intro y
    rw [le_floorRatPow_iff (by norm_num), pow_one, pow_one]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

open SubNLogN.Math.Cost in
theorem frp_le (x e : ℕ) (he : 0 < e) : floorRatPow x 1 e ≤ x := by
  have h := (le_floorRatPow_iff (x := x) (e₁ := 1) he (floorRatPow x 1 e)).1 le_rfl
  rw [pow_one] at h
  rcases Nat.eq_zero_or_pos (floorRatPow x 1 e) with h0 | h0
  · rw [h0]; exact Nat.zero_le _
  · exact le_trans (Nat.le_self_pow (by omega) _) h

open SubNLogN.Math.Cost in
theorem frp_iter (x n : ℕ) :
    floorRatPow (floorRatPow x 1 2) 1 (2 ^ n) = floorRatPow x 1 (2 ^ (n + 1)) := by
  have key : ∀ y, y ≤ floorRatPow (floorRatPow x 1 2) 1 (2 ^ n) ↔
      y ≤ floorRatPow x 1 (2 ^ (n + 1)) := by
    intro y
    rw [le_floorRatPow_iff (x := floorRatPow x 1 2) (e₁ := 1) (e₂ := 2 ^ n) (by positivity) y,
      le_floorRatPow_iff (x := x) (e₁ := 1) (e₂ := 2 ^ (n + 1)) (by positivity) y, pow_one,
      pow_one, le_floorRatPow_iff (x := x) (e₁ := 1) (e₂ := 2) (by norm_num) (y ^ 2 ^ n),
      pow_one, ← pow_mul, ← pow_succ]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem rootSearch_ms (e : ℕ) (he : 0 < e) (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u)
    (hY : u .Y = 0) :
    MS (search (testRoot e)) S0 u S0
      (Function.update u .Y (SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 e))
      ((SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 e + 1) *
        (rootB e (SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 e) (u .RAD) + 2) + 1) := by
  refine search_ms (testRoot e) (fun y => (y + 1) ^ e ≤ u .RAD) S0 u _ _ hY ?_ ?_ ?_
  · intro y hy v
    obtain ⟨t, ht, ev⟩ := testRoot_eval e S0 (Function.update u .Y y) (hc.upd rfl y) v
    simp only [Function.update_self,
      Function.update_of_ne (show RE.RAD ≠ RE.Y by decide)] at ht ev
    exact ⟨t, le_trans ht (rootB_mono e _ hy), ev⟩
  · intro y hy
    have h := (SubNLogN.Math.Cost.le_floorRatPow_iff (x := u .RAD) (e₁ := 1) he (y + 1)).1
      (by omega)
    simpa using h
  · intro h
    have h2 := (SubNLogN.Math.Cost.le_floorRatPow_iff (x := u .RAD) (e₁ := 1) he _).2
      (by simpa using h)
    omega

/-- `RAD := ⌊RAD ^ (1 / 2^n)⌋` by `n` integer square roots. -/
def iterSqrt : ℕ → SProg RK
  | 0 => skip
  | n + 1 => .seq (.seq (.seq (search (testRoot 2)) (clearM (.inr .RAD)))
      (moveAll (.inr .Y) (.inr .RAD))) (iterSqrt n)

/-- Cost bound of one square-root step on a radicand `≤ x`. -/
def sqB (x : ℕ) : ℕ := (x + 1) * (rootB 2 x x + 2) + 7 * x + 6

theorem sqB_mono {x x' : ℕ} (h : x ≤ x') : sqB x ≤ sqB x' := by
  unfold sqB rootB
  gcongr

theorem rootB_mono2 {x x' : ℕ} (h : x ≤ x') : rootB 2 x x ≤ rootB 2 x' x' := by
  unfold rootB
  gcongr

theorem iterSqrt_ms (S0 : RK → List Sym) : ∀ (n : ℕ) (u : RE → ℕ), ArClean u → u .Y = 0 →
    MS (iterSqrt n) S0 u S0
      (Function.update u .RAD (SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 (2 ^ n)))
      (n * sqB (u .RAD) + 1)
  | 0, u, _, _ => by
    refine ((MS.skip S0 u).of_eq rfl ?_).mono (by simp)
    rw [pow_zero, frp_one_one, Function.update_eq_self]
  | n + 1, u, hc, hY => by
    have hsx : SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 2 ≤ u .RAD := frp_le _ 2 (by norm_num)
    have h1 := rootSearch_ms 2 (by norm_num) S0 u hc hY
    have h := (h1.seq (clr_ms (a := .RAD) rfl S0 _)).seq
      (mv_ms (a := .Y) (b := .RAD) rfl rfl (by decide) S0 _)
    have h' : MS _ S0 u S0
        (Function.update u .RAD (SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 2)) _ :=
      h.of_eq rfl (by funext x; cases x <;> simp [hY])
    have ih := iterSqrt_ms S0 n
      (Function.update u .RAD (SubNLogN.Math.Cost.floorRatPow (u .RAD) 1 2)) (hc.upd rfl _)
      (by simp [hY])
    have h2 := h'.seq ih
    simp only [Function.update_self, Function.update_idem, frp_iter] at h2
    refine h2.mono ?_
    have m1 := Nat.mul_le_mul (Nat.add_le_add_right hsx 1)
      (Nat.add_le_add_right (rootB_mono 2 (u .RAD) hsx) 2)
    have m2 := Nat.mul_le_mul_left n (sqB_mono hsx)
    have m3 : (n + 1) * sqB (u .RAD) = n * sqB (u .RAD) +
        ((u .RAD + 1) * (rootB 2 (u .RAD) (u .RAD) + 2) + 7 * u .RAD + 6) := by
      unfold sqB; ring
    simp only [Function.update_of_ne (show RE.Y ≠ RE.RAD by decide), Function.update_self,
      Function.update_of_ne (show RE.RAD ≠ RE.Y by decide)]
    omega

/-! ## Ceiling division `Y := ⌈K / Dk⌉` -/

/-- Straight-line part of `testDiv`: `CA := Dk · Y + 1`, `CB := K`. -/
def divPre : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (.seq (.seq (copyAll (.inr .Y) (.inr .MA) (.inr .T))
    (copyAll (.inr .Dk) (.inr .MB) (.inr .T))) mulU) (clearM (.inr .MA))) (clearM (.inr .MB)))
    (pushC (.inr .MZ) .mark)) (moveAll (.inr .MZ) (.inr .CA)))
    (copyAll (.inr .K) (.inr .CB) (.inr .T))

/-- Test `Dk · Y + 1 ≤ K` (register `some` iff true); everything restored. -/
def testDiv : SProg RK := .seq divPre leTest

theorem divPre_ms (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u) :
    MS divPre S0 u S0 (Function.update (Function.update u .CA (u .Dk * u .Y + 1)) .CB (u .K))
      (25 * (u .Y + 1) * (u .Dk + 1) + 9 * u .K + 30) := by
  have hT : u .T = 0 := hc _ rfl
  have hA : u .MA = 0 := hc _ rfl
  have hB : u .MB = 0 := hc _ rfl
  have hZ : u .MZ = 0 := hc _ rfl
  have hB2 : u .MB2 = 0 := hc _ rfl
  have hCA : u .CA = 0 := hc _ rfl
  have hCB : u .CB = 0 := hc _ rfl
  have h := (((((((cp_ms (a := .Y) (b := .MA) (t := .T) rfl rfl rfl (by decide) (by decide)
    (by decide) S0 u hT).seq (cp_ms (a := .Dk) (b := .MB) (t := .T) rfl rfl rfl (by decide)
    (by decide) (by decide) S0 _ (by simp [hT]))).seq
    (mulU_ms S0 _ (by simp [hT]) (by simp [hB2]))).seq (clr_ms (a := .MA) rfl S0 _)).seq
    (clr_ms (a := .MB) rfl S0 _)).seq (push_ms (a := .MZ) rfl S0 _)).seq
    (mv_ms (a := .MZ) (b := .CA) rfl rfl (by decide) S0 _)).seq
    (cp_ms (a := .K) (b := .CB) (t := .T) rfl rfl rfl (by decide) (by decide) (by decide)
      S0 _ (by simp [hT]))
  refine (h.mono ?_).of_eq rfl ?_
  · simp only [Function.update_self, Function.update_idem, Function.update_of_ne, ne_eq,
      reduceCtorEq, not_false_eq_true, hA, hB, hZ, hCA, hCB, Nat.add_zero, Nat.zero_add]
    nlinarith [Nat.zero_le (u .Y * u .Dk)]
  · funext x
    cases x <;> simp [hA, hB, hZ, hCA, hCB] <;> ring

/-- Cost bound of one `testDiv` at `Y = y`, `Dk = d`, `K = k`. -/
def divB (y d k : ℕ) : ℕ := 25 * (y + 1) * (d + 1) + 15 * k + 6 * (d * y) + 48

theorem divB_mono (d k : ℕ) {y y' : ℕ} (h : y ≤ y') : divB y d k ≤ divB y' d k := by
  unfold divB
  gcongr

theorem testDiv_eval (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u) (v : Option Sym) :
    ∃ t, t ≤ divB (u .Y) (u .Dk) (u .K) ∧ Eval [] testDiv ⟨v, mkS S0 u⟩
      ⟨if u .Dk * u .Y + 1 ≤ u .K then some .mark else none, mkS S0 u⟩ t := by
  have hCA : u .CA = 0 := hc _ rfl
  have hCB : u .CB = 0 := hc _ rfl
  obtain ⟨r, t1, ht1, e1⟩ := divPre_ms S0 u hc v
  obtain ⟨t2, ht2, e2⟩ := leTest_eval r S0
    (Function.update (Function.update u .CA (u .Dk * u .Y + 1)) .CB (u .K))
  refine ⟨t1 + t2, ?_, (Eval.seq e1 e2).of_eq ?_ rfl⟩
  · simp only [Function.update_self, Function.update_of_ne, ne_eq, reduceCtorEq,
      not_false_eq_true] at ht2
    unfold divB
    omega
  · have hu : Function.update (Function.update (Function.update (Function.update u .CA
        (u .Dk * u .Y + 1)) .CB (u .K)) .CA 0) .CB 0 = u := by
      funext x
      cases x <;> simp [hCA, hCB]
    rw [hu]
    simp

theorem divSearch_ms (S0 : RK → List Sym) (u : RE → ℕ) (hc : ArClean u) (hY : u .Y = 0)
    (hd : u .Dk = 0 → u .K = 0) :
    MS (search testDiv) S0 u S0 (Function.update u .Y ((u .K + u .Dk - 1) / u .Dk))
      (((u .K + u .Dk - 1) / u .Dk + 1) *
        (divB ((u .K + u .Dk - 1) / u .Dk) (u .Dk) (u .K) + 2) + 1) := by
  refine search_ms testDiv (fun y => u .Dk * y + 1 ≤ u .K) S0 u _ _ hY ?_ ?_ ?_
  · intro y hy v
    obtain ⟨t, ht, ev⟩ := testDiv_eval S0 (Function.update u .Y y) (hc.upd rfl y) v
    simp only [Function.update_self, Function.update_of_ne (show RE.Dk ≠ RE.Y by decide),
      Function.update_of_ne (show RE.K ≠ RE.Y by decide)] at ht ev
    exact ⟨t, le_trans ht (divB_mono _ _ hy), ev⟩
  · intro y hy
    show u .Dk * y + 1 ≤ u .K
    rcases Nat.eq_zero_or_pos (u .Dk) with h0 | h0
    · rw [h0, hd h0] at hy
      simp at hy
    · have h1 := (Nat.le_div_iff_mul_le h0).1 (show y + 1 ≤ (u .K + u .Dk - 1) / u .Dk by omega)
      rw [Nat.add_mul, one_mul, Nat.mul_comm y] at h1
      omega
  · show ¬ (u .Dk * ((u .K + u .Dk - 1) / u .Dk) + 1 ≤ u .K)
    rcases Nat.eq_zero_or_pos (u .Dk) with h0 | h0
    · rw [h0, hd h0]
      simp
    · have h1 := Nat.div_add_mod (u .K + u .Dk - 1) (u .Dk)
      have h2 := Nat.mod_lt (u .K + u .Dk - 1) h0
      omega

/-! ## Truncated subtraction -/

/-- Loop body of `subU`. -/
def subBody (tgt : RE) : SProg RK :=
  .seq (.seq (popR (.inr .CA)) (popR (.inr tgt))) (peekR (.inr .CA))

/-- `tgt := tgt - src` (truncated); `src` restored. -/
def subU (src tgt : RE) : SProg RK :=
  .seq (.seq (copyAll (.inr src) (.inr .CA) (.inr .T)) (peekR (.inr .CA)))
    (.loop isSomeB (subBody tgt))

theorem sub_loop {tgt : RE} (ht : isU tgt = true) (htc : tgt ≠ .CA) (S0 : RK → List Sym) :
    ∀ (k : ℕ) (u : RE → ℕ), u .CA = k →
      Eval [] (.loop isSomeB (subBody tgt)) ⟨(List.replicate k Sym.mark).head?, mkS S0 u⟩
        ⟨none, mkS S0 (Function.update (Function.update u .CA 0) tgt (u tgt - k))⟩ (4 * k + 1)
  | 0, u, hk => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by ring)
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    congr 2
    funext x
    simp only [Function.update_apply]
    split_ifs <;> subst_vars <;> simp_all
  | k + 1, u, hk => by
    have e1 := popU_eval (a := .CA) rfl (List.replicate (k + 1) Sym.mark).head? S0 u
    have e2 := popU_eval (a := tgt) ht (List.replicate (u .CA) Sym.mark).head? S0
      (Function.update u .CA (u .CA - 1))
    set u2 := Function.update (Function.update u .CA (u .CA - 1)) tgt
      ((Function.update u .CA (u .CA - 1)) tgt - 1) with hu2
    have e3 := peekU_eval (a := .CA) rfl
      (List.replicate ((Function.update u .CA (u .CA - 1)) tgt) Sym.mark).head? S0 u2
    have h2C : u2 .CA = k := by
      rw [hu2, Function.update_of_ne (Ne.symm htc), Function.update_self, hk, Nat.add_sub_cancel]
    rw [h2C] at e3
    have ih := sub_loop ht htc S0 k u2 h2C
    have h2t : u2 tgt = u tgt - 1 := by
      rw [hu2, Function.update_self, Function.update_of_ne htc]
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) e3) ih).of_eq ?_ (by ring)
    congr 2
    rw [h2t, show u tgt - 1 - k = u tgt - (k + 1) by omega]
    funext x
    by_cases h1 : x = tgt
    · subst h1; simp only [Function.update_self]
    · by_cases h2 : x = .CA
      · subst h2; simp only [Function.update_of_ne h1, Function.update_self]
      · simp only [Function.update_of_ne h1, Function.update_of_ne h2, hu2]

theorem subU_ms {src tgt : RE} (hs : isU src = true) (ht : isU tgt = true) (hsc : src ≠ .CA)
    (htc : tgt ≠ .CA) (hst : src ≠ .T) (S0 : RK → List Sym) (u : RE → ℕ) (hT : u .T = 0)
    (hCA : u .CA = 0) :
    MS (subU src tgt) S0 u S0 (Function.update u tgt (u tgt - u src)) (13 * u src + 6) := by
  refine MS.of_eval fun v => ⟨none, ?_⟩
  have e1 := cpU_eval (a := src) (b := .CA) (t := .T) hs rfl rfl hsc hst (by decide) v S0 u hT
  rw [hCA, Nat.add_zero] at e1
  have e2 := peekU_eval (a := .CA) rfl none S0 (Function.update u .CA (u src))
  rw [Function.update_self] at e2
  have e3 := sub_loop ht htc S0 (u src) (Function.update u .CA (u src)) (Function.update_self _ _ _)
  refine (Eval.seq (Eval.seq e1 e2) e3).of_eq ?_ (by ring)
  congr 2
  funext x
  simp only [Function.update_apply]
  split_ifs <;> subst_vars <;> simp_all

end SubNLogN.Machine.Pipe.ReadParamsAux
