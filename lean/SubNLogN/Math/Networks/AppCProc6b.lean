import SubNLogN.Math.Networks.AppCProc6

/-!
# Appendix A procedures (V b): Lemma A.8 (`lem:transfer12`) for two binary fields whose widths differ by one bit

Lemma A.8 (`lem:transfer12`, last sentence: "Two fields whose widths differ
by one bit are interchanged across the intervening field by one such interchange and one single-bit
move") and its proof in Appendix A.3 (`sec:transfer-arbitrary`; the two field-order constructions of
[OAI26, §4.3, Lemma 12]). The machine-level contract
`C6InterchangeStmt` (`Machine/Contracts/AppC.lean`) allows `|u₁ − u₂| ≤ 1`; the equal-width case is
`InterchangeUCorrectStmt` (`AppCProc6.lean`).

Fields are reordered by *field relabellings* (`fieldTransport`): if field `i` of `L''` is field `σ i`
of `L` (same range), an address of `L''` is read as an address of `L`, and arrays transform by
`A ↦ A ∘ fieldTransport …` (pull convention, as `Step.run`). `rot3Perm n t₀ a s₀ b` reorders the three
consecutive blocks `[t₀, t₀+a)`, `[t₀+a, s₀)`, `[s₀, s₀+b)` into the order third, second, first (all
other fields fixed); `rot3Layout`/`rot3Run` are the reordered layout and array. Special cases: the
single-bit move of field `t₀` to position `s₀ − 1` is `rot3Perm n t₀ 1 s₀ 0`, and the move of field
`s₀` to position `t₀` is `rot3Perm n t₀ 0 s₀ 1`.

For chunks of `a` and `b` binary fields, `rot3Run L t₀ a s₀ b` is the interchange
`(…, h, g, d, …) ↦ (…, d, g, h, …)` of the two binary fields across the intervening field
(`h ∈ [2^a]`, `d ∈ [2^b]`, digits most significant first).
-/

namespace SubNLogN.Math.Networks

open Model

/-! ## Field relabellings -/

/-- Field relabelling: if field `i` of `L''` is field `σ i` of `L` (`hr`: same ranges), an address of
`L''` is read as an address of `L`. Arrays transform by `A ↦ A ∘ fieldTransport L L'' σ hr`. -/
def fieldTransport (L L'' : Layout) (σ : Fin L''.n ≃ Fin L.n) (hr : ∀ i, L''.r i = L.r (σ i)) :
    L''.Addr → L.Addr := fun y j =>
  Fin.cast ((hr (σ.symm j)).trans (congrArg L.r (σ.apply_symm_apply j))) (y (σ.symm j))

/-- The field of the reordered layout read at position `i`: blocks `[t₀, t₀+a)`, `[t₀+a, s₀)`,
`[s₀, s₀+b)` reordered third, second, first. -/
def rot3Fwd (t₀ a s₀ b i : ℕ) : ℕ :=
  if i < t₀ then i
  else if i < t₀ + b then s₀ + (i - t₀)
  else if i < s₀ + b - a then t₀ + a + (i - t₀ - b)
  else if i < s₀ + b then t₀ + (i - (s₀ + b - a))
  else i

/-- The position in the reordered layout of the original field `j` (inverse of `rot3Fwd`). -/
def rot3Bwd (t₀ a s₀ b j : ℕ) : ℕ :=
  if j < t₀ then j
  else if j < t₀ + a then s₀ + b - a + (j - t₀)
  else if j < s₀ then t₀ + b + (j - t₀ - a)
  else if j < s₀ + b then t₀ + (j - s₀)
  else j

/-- The reordering of the blocks `[t₀, t₀+a)`, `[t₀+a, s₀)`, `[s₀, s₀+b)` into the order third,
second, first, as a permutation of the fields: field `i` of the reordered layout is field
`rot3Perm n t₀ a s₀ b i` of the original. The identity unless `t₀ + a ≤ s₀` and `s₀ + b ≤ n`. -/
def rot3Perm (n t₀ a s₀ b : ℕ) : Equiv.Perm (Fin n) :=
  if H : t₀ + a ≤ s₀ ∧ s₀ + b ≤ n then
    { toFun := fun i => ⟨rot3Fwd t₀ a s₀ b i.val, by
        have := i.isLt; unfold rot3Fwd; split_ifs <;> omega⟩
      invFun := fun j => ⟨rot3Bwd t₀ a s₀ b j.val, by
        have := j.isLt; unfold rot3Bwd; split_ifs <;> omega⟩
      left_inv := fun i => by
        refine Fin.ext ?_
        have := i.isLt
        simp only
        unfold rot3Fwd rot3Bwd
        split_ifs <;> omega
      right_inv := fun j => by
        refine Fin.ext ?_
        have := j.isLt
        simp only
        unfold rot3Fwd rot3Bwd
        split_ifs <;> omega }
  else Equiv.refl _

/-- `L` with the blocks `[t₀, t₀+a)`, `[t₀+a, s₀)`, `[s₀, s₀+b)` reordered third, second, first
(reducible, so that `(rot3Layout L …).n` is `L.n` for type checking). -/
abbrev rot3Layout (L : Layout) (t₀ a s₀ b : ℕ) : Layout :=
  ⟨L.n, fun i => L.r (rot3Perm L.n t₀ a s₀ b i)⟩

/-- The reordered array: the blocks `[t₀, t₀+a)`, `[t₀+a, s₀)`, `[s₀, s₀+b)` of every address are
reordered third, second, first. -/
def rot3Run {β : Type} (L : Layout) (t₀ a s₀ b : ℕ) (A : L.Addr → β) :
    (rot3Layout L t₀ a s₀ b).Addr → β :=
  A ∘ fieldTransport L (rot3Layout L t₀ a s₀ b) (rot3Perm L.n t₀ a s₀ b) (fun _ => rfl)

/-! ## Contract -/

/-- CONTRACT (Lemma A.8 (`lem:transfer12`), widths differing by one bit;
Appendix A.3 (`sec:transfer-arbitrary`), [OAI26, §4.3, Lemma 12]). For every layout, payload type `β` and data,
the interchange of two binary fields of widths `u + 1` and `u` (either order) across the intervening
field (`rot3Run`, the full functional map `(a, h, g, d, z) ↦ (a, d, g, h, z)`) equals one equal-width
interchange of `u`-field chunks (`Step.swapBlocks`) composed with one single-bit move
(`rot3Perm … 1 … 0` or `rot3Perm … 0 … 1`):
* earlier field longer, `(h₀, H, G, D) → (h₀, D, G, H) → (D, G, h₀, H)`: chunks at `[t₀, t₀+u+1)` and
  `[s₀, s₀+u)`; swap `[t₀+1, t₀+1+u)` with `[s₀, s₀+u)`, then move field `t₀` to `s₀ − 1`;
* later field longer, `(H, G, d₀, D) → (d₀, H, G, D) → (d₀, D, G, H)`: chunks at `[t₀, t₀+u)` and
  `[s₀, s₀+u+1)`; move field `s₀` to `t₀`, then swap `[t₀+1, t₀+1+u)` with `[s₀+1, s₀+1+u)`.
In both cases the first conjunct says that the layout produced by the construction has the ranges of
the target layout field by field (so the final relabelling `h` exists); all chunk fields are binary.
Every `u` is allowed (`u = 0`: one single-bit move). The single-bit move is a field relayout
(`fieldTransport`, a value-level map, like the reshape maps of `AppCProc6.lean`); its machine
realization and step bound are in `SubNLogN/Machine/`. Payloads are an arbitrary type `β`, so complex records are covered
through the raw-word transport (`Proofs/RawTransport.lean`). -/
def Interchange6OffByOneStmt : Prop :=
  (∀ (L : Layout) (β : Type) (u t₀ s₀ : ℕ) (A : L.Addr → β),
    t₀ + (u + 1) ≤ s₀ → s₀ + u ≤ L.n →
    (∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + (u + 1)) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + u) →
      L.r i = 2) →
    (∀ i, (rot3Layout L t₀ (u + 1) s₀ u).r i = L.r (rot3Perm L.n t₀ 1 s₀ 0 i)) ∧
    ∀ h : ∀ i, (rot3Layout L t₀ (u + 1) s₀ u).r i = L.r (rot3Perm L.n t₀ 1 s₀ 0 i),
      rot3Run L t₀ (u + 1) s₀ u A =
        (Step.swapBlocks (t₀ + 1) s₀ u : Step L β).run A ∘
          fieldTransport L (rot3Layout L t₀ (u + 1) s₀ u) (rot3Perm L.n t₀ 1 s₀ 0) h) ∧
  (∀ (L : Layout) (β : Type) (u t₀ s₀ : ℕ) (A : L.Addr → β),
    t₀ + u ≤ s₀ → s₀ + (u + 1) ≤ L.n →
    (∀ i : Fin L.n, (t₀ ≤ i.val ∧ i.val < t₀ + u) ∨ (s₀ ≤ i.val ∧ i.val < s₀ + (u + 1)) →
      L.r i = 2) →
    (∀ i, (rot3Layout L t₀ u s₀ (u + 1)).r i = (rot3Layout L t₀ 0 s₀ 1).r i) ∧
    ∀ h : ∀ i, (rot3Layout L t₀ u s₀ (u + 1)).r i = (rot3Layout L t₀ 0 s₀ 1).r i,
      rot3Run L t₀ u s₀ (u + 1) A =
        (Step.swapBlocks (t₀ + 1) (s₀ + 1) u : Step (rot3Layout L t₀ 0 s₀ 1) β).run
            (rot3Run L t₀ 0 s₀ 1 A) ∘
          fieldTransport (rot3Layout L t₀ 0 s₀ 1) (rot3Layout L t₀ u s₀ (u + 1)) (Equiv.refl _) h)

end SubNLogN.Math.Networks
