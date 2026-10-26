import WP.W7k2.Canon.Series

/-!
# WP.W7k3.SeriesSpec — the series sub-kernel's contract (interface module)

The snapshot's fixed-point Taylor recurrence (`runRecurrenceSeriesCosted`, CTr:126; value part
`WP.W7k2.serState`) is run by one machine sub-kernel, shared by the `stdChar` (cos, sin) and the
`c0c1` (half-erf) kernels. A **series kind** `κ : SK` fixes the step factors

* `f k = fα·k + fβ` (`SK.f`) and `g k = (gγ·k + gδ)·(gε·k + gζ)` (`SK.g`),

with small constants (`SK.OK`). The kinds used by the snapshot's table primitives are `SK.cos`,
`SK.sin` (CTr:2347, 2357; also the sinc clamp), `SK.erf` (CTr:4838); `SK.*_f`, `SK.*_g` rewrite
them to the snapshot's lambdas.

`W7S_series _Mul` is the sub-kernel's contract, in the style of `Contracts.Machine.*`:
* stacks `0` = `a0` (signed), `1` = `c` (signed), `2` = `d` (unsigned, `> 0`), `3` = `n` (unsigned,
  `> 0`), all restored; `4` = destination, receiving `intSyms (serState a0 c d f g n).2`;
* ≤ 12 scratch stacks (a caller needs at least 17 host stacks);
* operand widths: exactly the snapshot's per-call-site predicate
  `IntMul.RecurrenceCallSitesWidthSound W a0 c d f g n` (every multiplication / division operand
  of every step fits in `W` bits);
* cost `C·(n+1)·(W+2)²`.

(The parameter `_Mul` is not used by the statement; it records the multiplication cost function of
`W7S_series_holds`, whose constant `C` depends on it.)
-/

namespace WP.W7k3

open TMFw TMFw.Contracts

/-- A series kind: the step factors `f k = fα·k + fβ`, `g k = (gγ·k + gδ)·(gε·k + gζ)`. -/
structure SK where
  fα : ℕ
  fβ : ℕ
  gγ : ℕ
  gδ : ℕ
  gε : ℕ
  gζ : ℕ

/-- The numerator step factor `f k = fα·k + fβ`. -/
def SK.f (κ : SK) (k : ℕ) : ℕ := κ.fα * k + κ.fβ

/-- The denominator step factor `g k = (gγ·k + gδ)·(gε·k + gζ)`. -/
def SK.g (κ : SK) (k : ℕ) : ℕ := (κ.gγ * k + κ.gδ) * (κ.gε * k + κ.gζ)

/-- Admissible kinds: small constants and `g k ≥ k + 1`. -/
def SK.OK (κ : SK) : Prop :=
  1 ≤ κ.gγ ∧ 1 ≤ κ.gδ ∧ 1 ≤ κ.gζ ∧ κ.fα ≤ 3 ∧ κ.fβ ≤ 3 ∧ κ.gγ ≤ 3 ∧ κ.gδ ≤ 3 ∧ κ.gε ≤ 3 ∧
    κ.gζ ≤ 3

/-- The cosine series (CTr:2347). -/
def SK.cos : SK := ⟨0, 1, 2, 1, 2, 2⟩

/-- The sine / sinc series (CTr:2357, 3263). -/
def SK.sin : SK := ⟨0, 1, 2, 2, 2, 3⟩

/-- The half-erf series (CTr:4838). -/
def SK.erf : SK := ⟨2, 1, 1, 1, 2, 3⟩

theorem SK.cos_f : SK.cos.f = fun _ => 1 := by
  funext k
  simp [SK.f, SK.cos]

theorem SK.cos_g : SK.cos.g = fun k => (2 * k + 1) * (2 * k + 2) := by
  funext k
  simp [SK.g, SK.cos]

theorem SK.sin_f : SK.sin.f = fun _ => 1 := by
  funext k
  simp [SK.f, SK.sin]

theorem SK.sin_g : SK.sin.g = fun k => (2 * k + 2) * (2 * k + 3) := by
  funext k
  simp [SK.g, SK.sin]

theorem SK.erf_f : SK.erf.f = fun k => 2 * k + 1 := by
  funext k
  simp [SK.f, SK.erf]

theorem SK.erf_g : SK.erf.g = fun k => (k + 1) * (2 * k + 3) := by
  funext k
  simp [SK.g, SK.erf]

theorem SK.cos_OK : SK.cos.OK := by
  unfold SK.OK SK.cos
  decide

theorem SK.sin_OK : SK.sin.OK := by
  unfold SK.OK SK.sin
  decide

theorem SK.erf_OK : SK.erf.OK := by
  unfold SK.OK SK.erf
  decide

/-- **The series sub-kernel's contract.** Stacks `0` = `a0`, `1` = `c` (signed), `2` = `d`,
`3` = `n` (unsigned), all restored; `4` = destination: `+= intSyms (serState a0 c d f g n).2`.
Cost `C·(n+1)·(W+2)²` under the snapshot's width predicate at width `W`. -/
def W7S_series (_Mul : ℕ → ℕ) : Prop :=
  MContract SK 5 12 Unit fun κ m _ C _ P => κ.OK →
    ∀ (W : ℕ) (a0 c : ℤ) (d n : ℕ) (r0 r1 r2 r3 : List Sym) (S : Loc 5 m → List Sym),
      0 < d → 0 < n → IntMul.RecurrenceCallSitesWidthSound W a0 c d κ.f κ.g n →
      TermOK r0 → TermOK r1 → TermOK r2 → TermOK r3 →
      S (.inl 0) = intSyms a0 ++ r0 → S (.inl 1) = intSyms c ++ r1 →
      S (.inl 2) = natSyms d ++ r2 → S (.inl 3) = natSyms n ++ r3 →
      Runs P S (Function.update S (.inl 4)
          (intSyms (WP.W7k2.serState a0 c d κ.f κ.g n).2 ++ S (.inl 4))) (fun _ => True)
        (C * (n + 1) * (W + 2) ^ 2)

#assert_std_axioms SK.cos_f SK.cos_g SK.sin_f SK.sin_g SK.erf_f SK.erf_g SK.cos_OK SK.sin_OK
  SK.erf_OK

end WP.W7k3
