import WP.W9g.CombN
import Mathlib.Tactic.Ring

/-!
# WP.W9g.FFTDefs — the recursive leaf FFT: program, invariant, cost, base case

`fftProg X = fix (ifTop CS optIsBit (stepProg X) (baseProg X))` is the recursive DIT radix-2 FFT
of PCP:2168-2185 (`fftV`). The stage `s` is the counter on top of `CS` (above a `mark`):
* `s = 0` (no bit on `CS`): `baseProg` rescales the single entry (`p_in → q`);
* `s = t + 1`: `unshProg`; `pushCnt`; `recur 0` (evens); `recur 0` (odds); `combProg` (stage `t`);
  `popCnt`.
`FInv s xs rest σ`: the input block `⟦xs⟧ $D` on top of `W0` (above `rest`), `s` on `CS`, and the
context `FCtx` (butterfly and rescale parameters, the table head at the LEAF body above the guard).
`outSt`: `W0 = rest`, `R` gets `⟦fftV s xs⟧` (reversed) and `$D`; every other stack is restored.
-/

namespace WP.W9g

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 Computability

theorem freeBelow_mono {K : Type} {Γ : K → Type} {σ : Type} :
    ∀ (p : Prog K Γ σ) {d d' : ℕ}, p.FreeBelow d → d ≤ d' → p.FreeBelow d'
  | .push .., _, _, _, _ => trivial
  | .peek .., _, _, _, _ => trivial
  | .pop .., _, _, _, _ => trivial
  | .load _, _, _, _, _ => trivial
  | .seq p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .ite _ p q, _, _, h, hd => ⟨freeBelow_mono p h.1 hd, freeBelow_mono q h.2 hd⟩
  | .loop _ p, _, _, h, hd => freeBelow_mono p h hd
  | .fix b, _, _, h, hd => freeBelow_mono b h (Nat.succ_le_succ hd)
  | .recur _, _, _, h, hd => Nat.lt_of_lt_of_le h hd

/-! ## Programs -/

section Prog

variable (X : Prims)

/-- An FFT node at stage `t + 1`. -/
def stepProg : MProg Stk X.Reg :=
  .seq unshProg (.seq pushCnt (.seq (.recur 0) (.seq (.recur 0) (.seq (combProg X) popCnt))))

/-- The FFT body. -/
def fftBody : MProg Stk X.Reg := ifTop .CS optIsBit (stepProg X) (baseProg X)

/-- The recursive leaf FFT. -/
def fftProg : MProg Stk X.Reg := .fix (fftBody X)

theorem fftProg_closed : (fftProg X).Closed :=
  ⟨trivial, ⟨freeBelow_mono _ (unshProg_closed (τ := X.Reg)) (Nat.zero_le 1),
    freeBelow_mono _ (pushCnt_closed (τ := X.Reg)) (Nat.zero_le 1), Nat.zero_lt_one,
    Nat.zero_lt_one, freeBelow_mono _ (combProg_closed X) (Nat.zero_le 1),
    freeBelow_mono _ (popCnt_closed (τ := X.Reg)) (Nat.zero_le 1)⟩,
    freeBelow_mono _ (baseProg_closed X) (Nat.zero_le 1)⟩

end Prog

/-! ## Invariant -/

/-- Stacks the FFT context depends on. -/
def fctxStk : List Stk := .SH :: .DIR :: .TR :: .TL :: (rsTemps ++ bfCtxStk)

/-- The FFT context: butterfly context, rescale parameters, the table head. -/
def FCtx (q K d : ℕ) (left : Bool) (tw : ℕ → ℕ → ℤ × ℤ) (restT L : List Sym)
    (σ : Stk → List Sym) : Prop :=
  BfCtx q σ ∧ (∃ rs, σ .SH = natSyms d ++ rs ∧ TermOK rs) ∧ (∃ rd, σ .DIR = dirSym left :: rd) ∧
    (∀ k ∈ rsTemps, TermOK (σ k)) ∧ σ .TR = leafTape K tw ++ restT ∧ σ .TL = symGuard :: L

theorem FCtx.frame {q K d : ℕ} {left : Bool} {tw : ℕ → ℕ → ℤ × ℤ} {restT L : List Sym}
    {σ σ' : Stk → List Sym} (h : FCtx q K d left tw restT L σ)
    (hag : ∀ k ∈ fctxStk, σ' k = σ k) : FCtx q K d left tw restT L σ' := by
  obtain ⟨hb, ⟨rs, hsh, hrs⟩, ⟨rd, hdir⟩, hT, htr, htl⟩ := h
  refine ⟨hb.frame (fun k hk => hag k ?_), ⟨rs, by rw [hag .SH (by decide), hsh], hrs⟩,
    ⟨rd, by rw [hag .DIR (by decide), hdir]⟩, fun k hk => ?_, by rw [hag .TR (by decide), htr],
    by rw [hag .TL (by decide), htl]⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inr hk)))))
  · rw [hag k (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl hk))))))]
    exact hT k hk

theorem FCtx.upd {q K d : ℕ} {left : Bool} {tw : ℕ → ℕ → ℤ × ℤ} {restT L : List Sym}
    {σ : Stk → List Sym} (h : FCtx q K d left tw restT L σ) {k : Stk} (hk : k ∉ fctxStk)
    (v : List Sym) : FCtx q K d left tw restT L (Function.update σ k v) :=
  h.frame (fun j hj => Function.update_of_ne (fun e : j = k => hk (e ▸ hj)) _ _)

/-- The FFT invariant at stage `s`: input `xs` on `W0` above `rest`. -/
def FInv (w pin q K d : ℕ) (left : Bool) (tw : ℕ → ℕ → ℤ × ℤ) (restT L : List Sym) (s : ℕ)
    (xs : List (ℤ × ℤ)) (rest : List Sym) (σ : Stk → List Sym) : Prop :=
  FCtx q K d left tw restT L σ ∧ s ≤ K ∧ xs.length = 2 ^ s ∧ (∀ z ∈ xs, EntryW w z) ∧
    fftW w pin q tw s xs ∧ (∃ cs0, σ .CS = natSyms s ++ Sym.mark :: cs0) ∧
    σ .W0 = blkE xs ++ symD :: rest

/-- The state after `FFT(s)`. -/
def outSt (pin q : ℕ) (tw : ℕ → ℕ → ℤ × ℤ) (s : ℕ) (xs : List (ℤ × ℤ)) (rest : List Sym)
    (σ : Stk → List Sym) : Stk → List Sym :=
  Function.update (Function.update σ .W0 rest) .R
    (blkE (fftV pin q tw s xs).reverse ++ symD :: σ .R)

/-! ## Cost -/

/-- Base-case bound (with the `ifTop` test). -/
def fftA (CL CA CR w d : ℕ) : ℕ := rescCost CL CA CR w d + 14 * eb w + 10

/-- Per-node overhead. -/
def fftO (K : ℕ) : ℕ := K * (6 * bitLen K + 20) + 33 * bitLen K + 82

/-- Per-output-entry cost of a node. -/
def fftB (cc w : ℕ) : ℕ := cc + 35 * eb w + 21

/-- Cost bound of the FFT body at stage `s`. -/
def fftCost (A O B : ℕ) : ℕ → ℕ
  | 0 => A
  | s + 1 => 2 * fftCost A O B s + O + 2 ^ (s + 1) * B

theorem fftCost_le (A O B : ℕ) : ∀ s, fftCost A O B s + O ≤ 2 ^ s * (A + O + s * B)
  | 0 => by simp [fftCost]
  | s + 1 => by
    have ih := fftCost_le A O B s
    have e : 2 ^ (s + 1) * (A + O + (s + 1) * B) =
        2 * (2 ^ s * (A + O + s * B)) + 2 ^ (s + 1) * B := by ring
    simp only [fftCost]
    omega

/-- The step-node cost fits the recursion. -/
theorem step_cost_le (cc w K t F fc : ℕ) (htK : t < K) (hF : F ≤ 2 ^ (t + 1) * eb w + t) :
    2 ^ t * (24 * eb w + 18) + 11 + (23 * bitLen (t + 1) + 27 + (fc + 2 + (fc + 2 +
      (combCost cc w (2 ^ t) t F + (3 * bitLen t + 3))))) + 2 ≤
    2 * fc + fftO K + 2 ^ (t + 1) * fftB cc w := by
  have h1 : bitLen (t + 1) ≤ bitLen K := bitLen_mono' (show t + 1 ≤ K by omega)
  have h2 : bitLen t ≤ bitLen K := bitLen_mono' (show t ≤ K by omega)
  have h3 : t * (6 * bitLen t + 14) ≤ K * (6 * bitLen K + 14) :=
    Nat.mul_le_mul (by omega) (by omega)
  have key : 2 ^ t * (24 * eb w + 18) + 2 ^ t * (2 * cc + 34 * eb w + 24) +
      6 * (2 ^ (t + 1) * eb w) = 2 ^ (t + 1) * fftB cc w := by
    unfold fftB
    ring
  have hO : fftO K = K * (6 * bitLen K + 14) + 6 * K + 33 * bitLen K + 82 := by
    unfold fftO
    ring
  unfold combCost
  omega

/-! ## The base case -/

theorem fftBase_rs {X : Prims} {Mul : ℕ → ℕ} {CM CA CS CL CR : ℕ}
    (hok : X.OK Mul CM CA CS CL CR) (w pin q K d : ℕ) (left : Bool) (tw : ℕ → ℕ → ℤ × ℤ)
    (restT L : List Sym) (hld : ∀ a, rescLD left d a = rescV pin q a)
    (ρ : List (MProg Stk X.Reg)) (xs : List (ℤ × ℤ)) (rest : List Sym) (σ : Stk → List Sym)
    (hinv : FInv w pin q K d left tw restT L 0 xs rest σ) :
    RS ρ (fftBody X) σ (outSt pin q tw 0 xs rest σ) (fftA CL CA CR w d) := by
  obtain ⟨⟨-, ⟨rs, hsh, hrs⟩, ⟨rd, hdir⟩, hT, -, -⟩, -, hlen, hWx, hW, ⟨cs0, hcs⟩, h0⟩ := hinv
  rcases xs with _ | ⟨⟨a, b⟩, _ | ⟨y, ys⟩⟩
  · simp at hlen
  · have h0' : σ .W0 = entrySyms (a, b) ++ symD :: rest := by
      rw [h0, blkE_cons, blkE_nil, List.append_nil]
    have hr : rescP pin q (a, b) = (rescLD left d a, rescLD left d b) := by
      simp only [rescP, hld]
    have hf : fftV pin q tw 0 [(a, b)] = [(rescLD left d a, rescLD left d b)] :=
      congrArg (fun z => [z]) hr
    have hw : EntryW w (a, b) := hWx _ (List.mem_singleton_self _)
    have hw' : EntryW w (rescLD left d a, rescLD left d b) :=
      hW.2 _ (by rw [hf]; exact List.mem_singleton_self _)
    refine ifTop_rs' (T := rescCost CL CA CR w d + 14 * eb w + 8) (fun hc => ?_) (fun _ => ?_) ?_
    · exfalso
      rw [hcs] at hc
      simp [natSyms, encodeNat_zero, optIsBit] at hc
    · refine ((base_rs hok left w d a b rest rs rd σ h0' hsh hrs hdir hT hw hw').env
        (baseProg_closed X) _).congr ?_ le_rfl
      unfold outSt
      rw [hf]
      simp only [List.reverse_singleton, blkE_cons, blkE_nil, List.append_nil]
    · unfold fftA
      omega
  · simp at hlen

#assert_std_axioms freeBelow_mono fftProg_closed FCtx.frame FCtx.upd fftCost_le step_cost_le
  fftBase_rs

end WP.W9g
