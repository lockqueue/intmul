import Contracts.Machine.Common
import IntMulTM.Framework.Lib.Basic

/-!
# Contracts.Machine.W4 — routing kernels: matrix transpose and affine odd-stride route

Conventions: `Contracts.Machine.Common` (`MContract`, `Runs`, `natSyms`, exact final stacks, so
every unmentioned stack, including the ≤ 4 scratch stacks, is restored). Specific to W4:

* **Records.** A record is a payload of data symbols (bits, `pos`, `neg`, `sep2`) followed by the
  record end `sep` (`⊣`): `RecOK r`. Records are self-delimiting, opaque to W4, and of variable
  length.
  * Complex records `sgn·bits(re)·sgn·bits(im)·⊣` are `RecOK`.
  * Level-stream entries can be encoded the same way, or with `sep2` as the internal field separator.
* **Blocks and orientation.** `blk .down v` puts the first record on top, each record
  in normal symbol order. `blk .up v = (blk .down v).reverse`: the last record is on top and each
  record is reversed internally.
  * One pop/push transfer of a whole block turns `.down` into `.up` and back.
  * Input and output orientation are **contract parameters** (`oi`, `oo`), so each layout
    instantiates the variant it needs, e.g. standard `Transp`/`OddRoute` with `oi = oo = .down`.
* **Block end.** The symbol after the input block is the stack bottom or a non-data, non-`sep`
  symbol (`BlkTerm`), e.g. a layout tag. The dimensions are also given, as binary counters on
  parameter stacks, which are restored. Transpose dimensions are powers of two (`2^a × 2^b`, as in
  the snapshot); the counters hold the exponents.
* **Effect.** The input block is consumed (the source becomes `rest`) and the routed block is
  pushed onto the destination's previous content.
* **Cost** is measured in symbols `|blk|`, so variable-length records are handled. Lower-order terms
  are explicit.

Relation to the snapshot (W9 bridges these; not proved here):
* `transposeL (2^a) (2^m)` is `runMultiTapeTranspose m (2^a)`, by
  `read1D_runMultiTapeTranspose_index_eq : out (j1·r + i) = tape (i·2^m + j1)`, SequentialTransducers:810.
* `oddRouteL k w b` is `runMultiTapeAffineOddRoute k w b`, by
  `read1D_runMultiTapeAffineOddRoute_index_eq : out u1 = col ((w·u1 + b) % 2^k)`, SequentialTransducers:974.
  The pipeline uses `w = oddStrideFactor m u2`, `b = 0`; `W4_oddStrideFactor` computes `w`, and
  `computableOddStrideFactor_param` (proved) shows it meets `W4_oddRoute`'s precondition.

**Mutation-test ideas.**
* A transpose that swaps `rows` and `cols` (outputs `transposeL cols rows v`) fails on any
  non-square example; see the `example` below.
* A transpose that seeks per record (`Θ(|blk|·2^a)`) violates the `min a b + 1` factor for large `a = b`.
* An odd-stride factor computed for `2·u2 + 1` instead of `2·u2 − 1` fails the pinned examples below.
* An odd route that ignores `b` fails at `k = 1, w = 1, b = 1`.
* A kernel that leaves a scratch mark behind fails the exact-frame post-state.
-/

namespace TMFw.Contracts

/-! ## Records and blocks -/

/-- Payload symbols of a record: bits, signs, and the internal field separator `sep2`. -/
def isDataSym : Sym → Bool
  | .bit _ => true
  | .pos => true
  | .neg => true
  | .sep2 => true
  | _ => false

/-- A record: data payload, then the record end `sep` (`⊣`). -/
def RecOK (r : List Sym) : Prop :=
  ∃ d : List Sym, r = d ++ [Sym.sep] ∧ ∀ x ∈ d, isDataSym x = true

/-- Block orientation (`.down` = first record on top; `.up` = reversed). -/
inductive Orient
  /-- first record on top, records in normal symbol order (`⟦v⟧↓`) -/
  | down
  /-- symbol reversal of `down`: last record on top, each record reversed (`⟦v⟧↑`) -/
  | up
  deriving DecidableEq

/-- Stack content of a block of records in orientation `o`. -/
def blk : Orient → List (List Sym) → List Sym
  | .down, v => v.flatten
  | .up, v => v.flatten.reverse

/-- What may follow a block: the bottom, or a symbol that is neither payload nor record end. -/
def BlkTerm (rest : List Sym) : Prop :=
  ∀ d, rest.head? = some d → isDataSym d = false ∧ d ≠ Sym.sep

/-! ## Pure index specifications -/

/-- Row-major transpose: the input is `rows × cols`, the output `cols × rows`; output entry
`j·rows + i` is input entry `i·cols + j`. -/
def transposeL {α : Type} [Inhabited α] (rows cols : ℕ) (v : List α) : List α :=
  (List.range (cols * rows)).map fun k => v.getD ((k % rows) * cols + k / rows) default

/-- Affine odd-stride routing of a column of `2^k` entries: output `u ↦ v[(w·u + b) mod 2^k]`. -/
def oddRouteL {α : Type} [Inhabited α] (k w b : ℕ) (v : List α) : List α :=
  (List.range (2 ^ k)).map fun u => v.getD ((w * u + b) % 2 ^ k) default

/-- Sanity: a `2 × 3` matrix. -/
example : transposeL 2 3 [0, 1, 2, 3, 4, 5] = [0, 3, 1, 4, 2, 5] := by decide

/-- Sanity: the swapped-dimension mutant differs. -/
example : transposeL 3 2 [0, 1, 2, 3, 4, 5] ≠ [0, 3, 1, 4, 2, 5] := by decide

/-- Sanity: `u ↦ (3u + 1) mod 4`. -/
example : oddRouteL 2 3 1 [10, 11, 12, 13] = [11, 10, 13, 12] := by decide

/-! ## Contracts -/

/-- **W4.transpose** (power-of-two dimensions, as in the snapshot), orientations `oi` in and `oo`
out. The input is `2^a × 2^b`, the output `2^b × 2^a`.
* Named stacks: `0` source block (consumed to `rest`), `1` destination (receives
  `blk oo (transposeL (2^a) (2^b) v)` on top), `2` = `a` and `3` = `b` (binary exponents,
  restored).
* Up to 4 scratch stacks.
* Cost `C·(|blk|+1)·(min a b + 1) + C·(|a| + |b| + 1)`; `min a b = log₂ min(rows, cols)`. -/
def W4_transpose (oi oo : Orient) : Prop :=
  MContract Unit 4 4 Unit fun _ m _ C _ P =>
    ∀ (a b : ℕ) (v : List (List Sym)) (rest r2 r3 : List Sym) (S : Loc 4 m → List Sym),
      v.length = 2 ^ a * 2 ^ b → (∀ r ∈ v, RecOK r) → BlkTerm rest → TermOK r2 → TermOK r3 →
      S (.inl 0) = blk oi v ++ rest → S (.inl 2) = natSyms a ++ r2 →
      S (.inl 3) = natSyms b ++ r3 →
      Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (blk oo (transposeL (2 ^ a) (2 ^ b) v) ++ S (.inl 1))) (fun _ => True)
        (C * ((blk oi v).length + 1) * (min a b + 1) + C * (bitLen a + bitLen b + 1))

/-! ## The odd-stride factor (snapshot definitions, restated verbatim) -/

/-- Snapshot `oddModInvPow2Iter` (ComputablePrimitives.lean:44): Hensel / Newton iteration for the
inverse of an odd `a` modulo `2^m`. -/
def oddModInvPow2Iter (m : ℕ) (a : ℤ) : ℕ → ℤ
  | 0 => 1
  | s + 1 =>
    let inv := oddModInvPow2Iter m a s
    (inv * (2 - a * inv)) % ((2 ^ m : ℕ) : ℤ)

/-- Snapshot `computableOddStrideInvPow2` (ComputablePrimitives.lean:52): `v1 < 2^k1` with
`(2·u2 − 1)·v1 ≡ u1 (mod 2^k1)`. -/
def computableOddStrideInvPow2 (k1 u2 u1 : ℕ) : ℕ :=
  let M : ℤ := ((2 ^ k1 : ℕ) : ℤ)
  let a : ℤ := 2 * (u2 : ℤ) - 1
  let inv : ℤ := oddModInvPow2Iter k1 a k1
  (((inv * (u1 : ℤ)) % M + M) % M).toNat

/-- Snapshot `computableOddStrideFactor` (ComputableExactSolvers.lean:762; the snapshot proves
`computableOddStrideFactor_eq_oddStrideFactor`): the multiplier used as
`runMultiTapeAffineOddRoute m (oddStrideFactor m u2) 0`. -/
def computableOddStrideFactor (m u2 : ℕ) : ℕ :=
  if m = 0 then 1 else computableOddStrideInvPow2 m u2 1

example : computableOddStrideFactor 0 5 = 1 := by decide
example : computableOddStrideFactor 3 0 = 7 := by decide
example : computableOddStrideFactor 3 2 = 3 := by decide
example : computableOddStrideFactor 4 3 = 13 := by decide

/-- Admissible multipliers of `W4_oddRoute`: odd, and reduced (`w < 2^(k+1)`). -/
def OddRouteParam (k w : ℕ) : Prop := w % 2 = 1 ∧ w < 2 ^ (k + 1)

theorem two_dvd_two_pow {k : ℕ} (hk : k ≠ 0) : (2 : ℤ) ∣ ((2 ^ k : ℕ) : ℤ) := by
  have h : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← Nat.pow_succ']
    congr 1
    omega
  exact Int.ofNat_dvd.mpr ⟨_, h⟩

/-- Parity invariant of the Hensel iteration: odd `a`, even modulus `2^m`. -/
theorem oddModInvPow2Iter_odd (m : ℕ) (a : ℤ) (hm : m ≠ 0) (ha : a % 2 = 1) :
    ∀ s, oddModInvPow2Iter m a s % 2 = 1
  | 0 => by
    show (1 : ℤ) % 2 = 1
    decide
  | s + 1 => by
    have ih := oddModInvPow2Iter_odd m a hm ha s
    show oddModInvPow2Iter m a s * (2 - a * oddModInvPow2Iter m a s) % ((2 ^ m : ℕ) : ℤ) % 2 = 1
    rw [Int.emod_emod_of_dvd _ (two_dvd_two_pow hm), Int.mul_emod, ih, Int.sub_emod,
      Int.mul_emod a, ha, ih]
    decide

theorem normMod_props (x M : ℤ) (hM : 0 < M) (h2 : (2 : ℤ) ∣ M) (hx : x % 2 = 1) :
    ((x % M + M) % M).toNat % 2 = 1 ∧ ((x % M + M) % M).toNat < M.toNat := by
  have hy0 : 0 ≤ (x % M + M) % M := Int.emod_nonneg _ (Int.ne_of_gt hM)
  have hy1 : (x % M + M) % M < M := Int.emod_lt_of_pos _ hM
  have hM2 : M % 2 = 0 := Int.emod_eq_zero_of_dvd h2
  have hy2 : (x % M + M) % M % 2 = 1 := by
    rw [Int.emod_emod_of_dvd _ h2, Int.add_emod, Int.emod_emod_of_dvd _ h2, hM2, hx]
    decide
  have hc : (((x % M + M) % M).toNat : ℤ) = (x % M + M) % M := Int.toNat_of_nonneg hy0
  have hMc : ((M.toNat : ℕ) : ℤ) = M := Int.toNat_of_nonneg (Int.le_of_lt hM)
  constructor <;> omega

/-- **Wiring (proved):** the factor computed by `W4_oddStrideFactor` is an admissible
`W4_oddRoute` multiplier. -/
theorem computableOddStrideFactor_param (k u2 : ℕ) :
    OddRouteParam k (computableOddStrideFactor k u2) := by
  unfold OddRouteParam computableOddStrideFactor
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    unfold computableOddStrideInvPow2
    dsimp only
    have hMpos : (0 : ℤ) < ((2 ^ k : ℕ) : ℤ) := Int.ofNat_lt.mpr (Nat.two_pow_pos k)
    have hodd := oddModInvPow2Iter_odd k (2 * (u2 : ℤ) - 1) hk (by omega) k
    have hx : (oddModInvPow2Iter k (2 * (u2 : ℤ) - 1) k * ((1 : ℕ) : ℤ)) % 2 = 1 := by
      rw [Int.mul_emod, hodd]
      decide
    obtain ⟨h1, h2⟩ := normMod_props _ _ hMpos (two_dvd_two_pow hk) hx
    refine ⟨h1, ?_⟩
    rw [Int.toNat_natCast] at h2
    have h4 : 2 ^ (k + 1) = 2 ^ k * 2 := Nat.pow_succ 2 k
    omega

/-- **W4.oddStrideFactor**: compute the snapshot's multiplier `computableOddStrideFactor k u2`
(`1` if `k = 0`; else the inverse of `2·u2 − 1` mod `2^k`).
* Named stacks: `0` = `k`, `1` = `u2` (binary, restored), `2` = destination (the factor is pushed).
* Cost `C·((k+1)² + |u2|)`. The bitwise Hensel lift is `O(k²)`, and only the low `k` bits of `u2`
  matter. -/
def W4_oddStrideFactor : Prop :=
  MContract Unit 3 4 Unit fun _ m _ C _ P =>
    ∀ (k u2 : ℕ) (r0 r1 : List Sym) (S : Loc 3 m → List Sym), TermOK r0 → TermOK r1 →
      S (.inl 0) = natSyms k ++ r0 → S (.inl 1) = natSyms u2 ++ r1 →
      Runs P S (Function.update S (.inl 2) (natSyms (computableOddStrideFactor k u2) ++ S (.inl 2)))
        (fun _ => True) (C * ((k + 1) ^ 2 + bitLen u2))

/-- **W4.oddRoute** with orientations `oi`, `oo`: route a column of `2^k` records by
`u ↦ (w·u + b) mod 2^k`.
* Preconditions: `OddRouteParam k w` (odd, reduced; satisfied by `computableOddStrideFactor k u2`,
  see `computableOddStrideFactor_param`, so `W4_oddStrideFactor` composes directly) and `b < 2^k`.
  The pipeline uses `b = 0`.
* Named stacks: `0` source column (consumed to `rest`), `1` destination, `2` = `k`, `3` = `w`,
  `4` = `b` (binary, restored).
* Cost `C·(|blk|+1)·(k+1)`. The parameter arithmetic, `O(k)` per recursion node, is absorbed since
  `|blk| ≥ 2^k`. -/
def W4_oddRoute (oi oo : Orient) : Prop :=
  MContract Unit 5 4 Unit fun _ m _ C _ P =>
    ∀ (k w b : ℕ) (v : List (List Sym)) (rest r2 r3 r4 : List Sym) (S : Loc 5 m → List Sym),
      OddRouteParam k w → b < 2 ^ k → v.length = 2 ^ k → (∀ r ∈ v, RecOK r) →
      BlkTerm rest → TermOK r2 → TermOK r3 → TermOK r4 →
      S (.inl 0) = blk oi v ++ rest → S (.inl 2) = natSyms k ++ r2 →
      S (.inl 3) = natSyms w ++ r3 → S (.inl 4) = natSyms b ++ r4 →
      Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (blk oo (oddRouteL k w b v) ++ S (.inl 1))) (fun _ => True)
        (C * ((blk oi v).length + 1) * (k + 1))

/-- Orientation bookkeeping used by integrators: `up` is the symbol reversal of `down`. -/
theorem blk_up (v : List (List Sym)) : blk .up v = (blk .down v).reverse := rfl

/-! ## A proved primitive: moving one record (non-vacuity) -/

/-- **W4.moveRecord**: move the top record of stack `0` onto stack `1`. One transfer reverses the
record's symbol order, which flips its orientation. Cost `C·(|r|+1)`. -/
def W4_moveRecord : Prop :=
  MContract Unit 2 4 Unit fun _ m _ C _ P =>
    ∀ (r rest : List Sym) (S : Loc 2 m → List Sym), RecOK r →
      S (.inl 0) = r ++ rest →
      Runs P S (Function.update (Function.update S (.inl 0) rest) (.inl 1)
          (r.reverse ++ S (.inl 1))) (fun _ => True) (C * (r.length + 1))

/-- Register holds a payload symbol. -/
def isDataR : Option Sym → Bool
  | some x => isDataSym x
  | none => false

/-- Loop body: push the register onto `dst`, pop `src`. -/
def moveRecBody {K : Type} (src dst : K) : Prog K (fun _ => Sym) (Option Sym) :=
  .seq (Lib.pushR dst) (Lib.popR src)

/-- Move one record: pop, transfer the payload, then push the record end. -/
def moveRec {K : Type} (src dst : K) : Prog K (fun _ => Sym) (Option Sym) :=
  .seq (Lib.popR src) (.seq (.loop isDataR (moveRecBody src dst)) (Lib.pushR dst))

theorem moveRec_loop_eval {K : Type} [DecidableEq K] {src dst : K} (hne : src ≠ dst) :
    ∀ (d rest : List Sym) (S : K → List Sym), (∀ x ∈ d, isDataSym x = true) →
      S src = (d ++ Sym.sep :: rest).tail →
      Eval [] (.loop isDataR (moveRecBody src dst)) ⟨(d ++ Sym.sep :: rest).head?, S⟩
        ⟨some Sym.sep, Function.update (Function.update S src rest) dst (d.reverse ++ S dst)⟩
        (3 * d.length + 1)
  | [], rest, S, _, hS => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    have hS' : S src = rest := hS
    show (⟨some Sym.sep, S⟩ : St K (fun _ => Sym) (Option Sym)) =
      ⟨some Sym.sep, Function.update (Function.update S src rest) dst ([].reverse ++ S dst)⟩
    rw [← hS', Function.update_eq_self, List.reverse_nil, List.nil_append, Function.update_eq_self]
  | x :: d, rest, S, hd, hS => by
    have hx : isDataSym x = true := hd x (by simp)
    have hd' : ∀ y ∈ d, isDataSym y = true := fun y hy => hd y (by simp [hy])
    have hS' : S src = d ++ Sym.sep :: rest := hS
    have hpush : Eval [] (Lib.pushR dst) ⟨some x, S⟩
        ⟨some x, Function.update S dst (x :: S dst)⟩ 1 :=
      Eval.push _ _ _ _ _
    have hsrc : Function.update S dst (x :: S dst) src = d ++ Sym.sep :: rest := by
      rw [Function.update_of_ne hne]
      exact hS'
    have hpop : Eval [] (Lib.popR src) ⟨some x, Function.update S dst (x :: S dst)⟩
        ⟨(d ++ Sym.sep :: rest).head?, Function.update (Function.update S dst (x :: S dst))
          src (d ++ Sym.sep :: rest).tail⟩ 1 := by
      refine (Eval.pop [] src (fun _ o => o) _ _).of_eq ?_ rfl
      rw [hsrc]
    have ih := moveRec_loop_eval hne d rest
      (Function.update (Function.update S dst (x :: S dst)) src (d ++ Sym.sep :: rest).tail) hd'
      (Function.update_self _ _ _)
    refine (Eval.loop_true hx (Eval.seq hpush hpop) ih).of_eq ?_ ?_
    · congr 1
      funext k
      simp only [Function.update_apply, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      split_ifs <;> simp_all
    · simp only [List.length_cons]
      omega

theorem moveRec_eval {K : Type} [DecidableEq K] {src dst : K} (hne : src ≠ dst) (v : Option Sym)
    (d rest : List Sym) (S : K → List Sym) (hd : ∀ x ∈ d, isDataSym x = true)
    (hS : S src = d ++ Sym.sep :: rest) :
    Eval [] (moveRec src dst) ⟨v, S⟩
      ⟨some Sym.sep, Function.update (Function.update S src rest) dst
        (Sym.sep :: (d.reverse ++ S dst))⟩ (3 * d.length + 3) := by
  have h1 : Eval [] (Lib.popR src) ⟨v, S⟩
      ⟨(d ++ Sym.sep :: rest).head?, Function.update S src (d ++ Sym.sep :: rest).tail⟩ 1 := by
    refine (Eval.pop [] src (fun _ o => o) v S).of_eq ?_ rfl
    rw [hS]
  have h2 := moveRec_loop_eval hne d rest (Function.update S src (d ++ Sym.sep :: rest).tail) hd
    (Function.update_self _ _ _)
  set S2 := Function.update (Function.update (Function.update S src (d ++ Sym.sep :: rest).tail)
    src rest) dst (d.reverse ++ Function.update S src (d ++ Sym.sep :: rest).tail dst) with hS2
  have h3 : Eval [] (Lib.pushR dst) ⟨some Sym.sep, S2⟩
      ⟨some Sym.sep, Function.update S2 dst (Sym.sep :: S2 dst)⟩ 1 :=
    Eval.push _ _ _ _ _
  refine (Eval.seq h1 (Eval.seq h2 h3)).of_eq ?_ (by omega)
  congr 1
  funext k
  simp only [hS2, Function.update_apply]
  split_ifs <;> simp_all

theorem w4_moveRecord : W4_moveRecord := by
  refine ⟨3, fun _ => ⟨0, Option Sym, fun _ => (), moveRec (.inl 0) (.inl 1), Nat.zero_le _,
    inferInstance, ⟨none⟩, ?_, ?_⟩⟩
  · simp [Prog.Closed, Prog.FreeBelow, moveRec, moveRecBody, Lib.pushR, Lib.popR]
  · rintro r rest S ⟨d, rfl, hd⟩ hS
    refine Runs.of_eval fun v => ⟨some Sym.sep, _,
      (moveRec_eval (src := .inl 0) (dst := .inl 1) (by decide) v d rest S hd
        (by rw [hS, List.append_assoc, List.singleton_append])).of_eq ?_ rfl, trivial, ?_⟩
    · simp [List.reverse_append]
    · simp only [List.length_append, List.length_singleton]
      omega

#assert_std_axioms blk_up moveRec_loop_eval moveRec_eval w4_moveRecord two_dvd_two_pow
  oddModInvPow2Iter_odd normMod_props computableOddStrideFactor_param

end TMFw.Contracts
