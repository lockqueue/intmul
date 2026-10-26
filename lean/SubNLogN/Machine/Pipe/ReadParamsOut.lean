import SubNLogN.Machine.Pipe.ReadParamsBase

/-!
# Read-parameters kernel, part 2: binary output, header arithmetic, header reading

Helpers (namespace `SubNLogN.Machine.Pipe.ReadParamsAux`):
* unary to binary: halving (`halve_eval`), `toBin_ms` (the bits of `NUM` on the bit buffer `O`),
  `bitLenU_ms` (`Z += bitLen NUM`), `pushNat_ms` (push `hdrSyms [NUM]` on a named stack),
  `pushPow2_ms` (push `hdrSyms [2 ^ NUM]`), `rep_ms` (repeat a field pusher `CNT` times);
* header arithmetic for the row `row46`: `dK46`, `KK46`, `lK46`, bounds (`dK46_le`, `dK46_pow`,
  `lK46_le`, `fnewM_le`), the lists `ofFn_fnewA`, `ofFn_fnewShape`, and
  `clog_eq_bitLen : Nat.clog 2 x = bitLen (x - 1)` (`1 ≤ x`);
* reading the header fields `b`, `K0` (stack `C0`) and `p_in` (stack `C1`) into unary registers,
  restoring `C0`, `C1` (`read_ms`).
-/

namespace SubNLogN.Machine.Pipe.ReadParamsAux

open Computability TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 SubNLogN.Machine
open SubNLogN.Machine.Pipe.GuardAux

/-! ## Bit buffer `O` and named stacks -/

theorem pushO_eval (x : Sym) (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (pushC (.inr .O) x) ⟨v, mkS S0 u⟩
      ⟨v, mkS (Function.update S0 (.inr .O) (x :: S0 (.inr .O))) u⟩ 1 := by
  have e := Eval.push [] (.inr .O) (fun _ => x) v (mkS S0 u)
  refine e.of_eq ?_ rfl
  rw [mkS_N (e := .O) rfl, upd_mkS_N (e := .O) rfl]

theorem popO_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (popR (.inr .O)) ⟨v, mkS S0 u⟩
      ⟨(S0 (.inr .O)).head?, mkS (Function.update S0 (.inr .O) (S0 (.inr .O)).tail) u⟩ 1 := by
  have e := Eval.pop [] (.inr .O) (fun _ o => o) v (mkS S0 u)
  refine e.of_eq ?_ rfl
  rw [mkS_N (e := .O) rfl, upd_mkS_N (e := .O) rfl]

theorem peekO_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (peekR (.inr .O)) ⟨v, mkS S0 u⟩ ⟨(S0 (.inr .O)).head?, mkS S0 u⟩ 1 := by
  have e := Eval.peek [] (.inr .O) (fun _ o => o) v (mkS S0 u)
  refine e.of_eq ?_ rfl
  rw [mkS_N (e := .O) rfl]

theorem pushL_eval (n : PN) (x : Sym) (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (pushC (.inl n) x) ⟨v, mkS S0 u⟩
      ⟨v, mkS (Function.update S0 (.inl n) (x :: S0 (.inl n))) u⟩ 1 := by
  have e := Eval.push [] (.inl n) (fun _ => x) v (mkS S0 u)
  refine e.of_eq ?_ rfl
  rw [mkS_inl, upd_mkS_inl]

/-! ## Halving, unary to binary -/

/-- Loop body of the halving pass: pop a pair from `NUM` and push one mark on `X`; an odd
leftover is recorded on `PAR`. -/
def halveBody : SProg RK :=
  .seq (.seq (popR (.inr .NUM)) (peekR (.inr .NUM)))
    (.ite isSomeB (.seq (.seq (popR (.inr .NUM)) (pushC (.inr .X) .mark)) (peekR (.inr .NUM)))
      (pushC (.inr .PAR) .mark))

theorem halve_loop (S0 : RK → List Sym) : ∀ (n : ℕ) (u : RE → ℕ), u .NUM = n →
    Eval [] (.loop isSomeB halveBody) ⟨(List.replicate n Sym.mark).head?, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update (Function.update (Function.update u .NUM 0) .X
        (u .X + n / 2)) .PAR (u .PAR + n % 2))⟩ (7 * (n / 2) + 5 * (n % 2) + 1)
  | 0, u, hn => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by norm_num)
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    congr 2
    funext x
    cases x <;> simp [hn]
  | 1, u, hn => by
    have e1 := popU_eval (a := .NUM) rfl (List.replicate 1 Sym.mark).head? S0 u
    rw [hn, Nat.sub_self] at e1
    have e2 := peekU_eval (a := .NUM) rfl (List.replicate 1 Sym.mark).head? S0
      (Function.update u .NUM 0)
    rw [Function.update_self] at e2
    have e3 := Eval.ite_false (c := isSomeB)
      (p := (.seq (.seq (popR (.inr .NUM)) (pushC (.inr .X) .mark)) (peekR (.inr .NUM)) :
        SProg RK)) (by rfl)
      (pushU_eval (a := .PAR) rfl (List.replicate 0 Sym.mark).head? S0 (Function.update u .NUM 0))
    have e4 := Eval.loop_false (ρ := []) (p := halveBody) (c := isSomeB)
      (s := ⟨(List.replicate 0 Sym.mark).head?, mkS S0 (Function.update (Function.update u .NUM 0)
        .PAR ((Function.update u .NUM 0) .PAR + 1))⟩) (by rfl)
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) e3) e4).of_eq ?_ (by norm_num)
    show (⟨none, _⟩ : SSt RK) = _
    congr 2
    funext x
    cases x <;> simp
  | n + 2, u, hn => by
    have e1 := popU_eval (a := .NUM) rfl (List.replicate (n + 2) Sym.mark).head? S0 u
    rw [hn, show n + 2 - 1 = n + 1 from rfl] at e1
    have e2 := peekU_eval (a := .NUM) rfl (List.replicate (n + 2) Sym.mark).head? S0
      (Function.update u .NUM (n + 1))
    rw [Function.update_self] at e2
    have e3 := popU_eval (a := .NUM) rfl (List.replicate (n + 1) Sym.mark).head? S0
      (Function.update u .NUM (n + 1))
    rw [Function.update_self, Function.update_idem, show n + 1 - 1 = n from rfl] at e3
    have e4 := pushU_eval (a := .X) rfl (List.replicate (n + 1) Sym.mark).head? S0
      (Function.update u .NUM n)
    set u5 := Function.update (Function.update u .NUM n) .X
      ((Function.update u .NUM n) .X + 1) with hu5
    have e5 := peekU_eval (a := .NUM) rfl (List.replicate (n + 1) Sym.mark).head? S0 u5
    have h5 : u5 .NUM = n := by simp [hu5]
    rw [h5] at e5
    have eite := Eval.ite_true (q := (pushC (.inr .PAR) .mark : SProg RK)) (c := isSomeB)
      (by rfl) (Eval.seq (Eval.seq e3 e4) e5)
    have ih := halve_loop S0 n u5 h5
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) eite) ih).of_eq ?_ ?_
    · congr 2
      funext x
      cases x <;> simp [hu5] <;> omega
    · omega

/-- Halving pass: `X += NUM / 2`, `PAR += NUM % 2`, `NUM := 0`. -/
def halve : SProg RK := .seq (peekR (.inr .NUM)) (.loop isSomeB halveBody)

theorem halve_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] halve ⟨v, mkS S0 u⟩
      ⟨none, mkS S0 (Function.update (Function.update (Function.update u .NUM 0) .X
        (u .X + u .NUM / 2)) .PAR (u .PAR + u .NUM % 2))⟩
      (7 * (u .NUM / 2) + 5 * (u .NUM % 2) + 2) := by
  have e0 := peekU_eval (a := .NUM) rfl v S0 u
  exact (Eval.seq e0 (halve_loop S0 (u .NUM) u rfl)).of_eq rfl (by ring)

/-- Emit the parity bit (`PAR ∈ {0,1}`) on the bit buffer `O`; `PAR := 0`. -/
def emitBit : SProg RK :=
  .seq (peekR (.inr .PAR)) (.ite isSomeB (.seq (popR (.inr .PAR)) (pushC (.inr .O) (.bit true)))
    (pushC (.inr .O) (.bit false)))

theorem emitBit_eval (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) (hP : u .PAR < 2) :
    ∃ r t, t ≤ 4 ∧ Eval [] emitBit ⟨v, mkS S0 u⟩
      ⟨r, mkS (Function.update S0 (.inr .O) (Sym.bit (decide (u .PAR = 1)) :: S0 (.inr .O)))
        (Function.update u .PAR 0)⟩ t := by
  have e0 := peekU_eval (a := .PAR) rfl v S0 u
  rcases (show u .PAR = 0 ∨ u .PAR = 1 by omega) with h | h
  · rw [h] at e0
    have e1 := Eval.ite_false (c := isSomeB)
      (p := (.seq (popR (.inr .PAR)) (pushC (.inr .O) (.bit true)) : SProg RK)) (by rfl)
      (pushO_eval (.bit false) (List.replicate 0 Sym.mark).head? S0 u)
    refine ⟨(List.replicate 0 Sym.mark).head?, _, by omega, (Eval.seq e0 e1).of_eq ?_ rfl⟩
    have hu : Function.update u .PAR 0 = u := by rw [← h, Function.update_eq_self]
    rw [hu, h]
    rfl
  · rw [h] at e0
    have e1 := popU_eval (a := .PAR) rfl (List.replicate 1 Sym.mark).head? S0 u
    rw [h, Nat.sub_self] at e1
    have e2 := pushO_eval (.bit true) (List.replicate 1 Sym.mark).head? S0
      (Function.update u .PAR 0)
    have e3 := Eval.ite_true (q := (pushC (.inr .O) (.bit false) : SProg RK)) (c := isSomeB)
      (by rfl) (Eval.seq e1 e2)
    refine ⟨(List.replicate 1 Sym.mark).head?, _, by omega, (Eval.seq e0 e3).of_eq ?_ rfl⟩
    rw [h]
    rfl

theorem encodeNat_pos (n : ℕ) (h : 0 < n) :
    encodeNat n = decide (n % 2 = 1) :: encodeNat (n / 2) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hk : 0 < k := by omega
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k) / 2 = k := by omega
    rw [h1, h2, show 2 * k = k + k by ring, encodeNat_add,
      if_neg (by rw [encodeNat_eq_nil_iff]; omega)]
    rfl
  · have h1 : (2 * k + 1) % 2 = 1 := by omega
    have h2 : (2 * k + 1) / 2 = k := by omega
    rw [h1, h2, show 2 * k + 1 = k + k + 1 by ring, encodeNat_add_add_one]
    rfl

theorem bitLen_le (n : ℕ) : bitLen n ≤ n := by
  unfold bitLen
  rw [IntMulTM.length_encodeNat, Nat.size_le]
  exact Nat.lt_two_pow_self

/-- One round of binary conversion: halve, emit the parity bit, move the half back. -/
def binBody : SProg RK :=
  .seq (.seq (.seq halve emitBit) (moveAll (.inr .X) (.inr .NUM))) (peekR (.inr .NUM))

/-- Binary conversion: the bits of `NUM` (LSB first) are pushed on the bit buffer `O` (so `O`
holds them MSB on top); `NUM := 0`. -/
def toBin : SProg RK := .seq (peekR (.inr .NUM)) (.loop isSomeB binBody)

theorem toBin_loop : ∀ (n : ℕ) (S0 : RK → List Sym) (u : RE → ℕ), u .NUM = n → u .X = 0 →
    u .PAR = 0 → ∃ t, t ≤ 30 * n + 1 ∧ Eval [] (.loop isSomeB binBody)
      ⟨(List.replicate n Sym.mark).head?, mkS S0 u⟩
      ⟨none, mkS (Function.update S0 (.inr .O)
        ((encodeNat n).reverse.map Sym.bit ++ S0 (.inr .O))) (Function.update u .NUM 0)⟩ t := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S0 u hn hX hP
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      refine ⟨1, by omega, (Eval.loop_false (by rfl)).of_eq ?_ rfl⟩
      show (⟨none, mkS S0 u⟩ : SSt RK) = _
      rw [encodeNat_zero, List.reverse_nil, List.map_nil, List.nil_append,
        Function.update_eq_self, ← hn, Function.update_eq_self]
    · have e1 := halve_eval (List.replicate n Sym.mark).head? S0 u
      rw [hn, hX, hP, Nat.zero_add, Nat.zero_add] at e1
      set u1 := Function.update (Function.update (Function.update u .NUM 0) .X (n / 2)) .PAR
        (n % 2) with hu1
      have hp1 : u1 .PAR = n % 2 := by simp [hu1]
      obtain ⟨r2, t2, ht2, e2⟩ := emitBit_eval none S0 u1 (by rw [hp1]; omega)
      rw [hp1] at e2
      set S1 := Function.update S0 (.inr .O) (Sym.bit (decide (n % 2 = 1)) :: S0 (.inr .O))
        with hS1
      have e3 := mvU_eval (a := .X) (b := .NUM) rfl rfl (by decide) r2 S1
        (Function.update u1 .PAR 0)
      set u3 := Function.update (Function.update (Function.update u1 .PAR 0) .X 0) .NUM
        ((Function.update u1 .PAR 0) .X + (Function.update u1 .PAR 0) .NUM) with hu3
      have e4 := peekU_eval (a := .NUM) rfl none S1 u3
      have h3N : u3 .NUM = n / 2 := by simp [hu3, hu1]
      rw [h3N] at e4
      obtain ⟨t5, ht5, e5⟩ := ih (n / 2) (by omega) S1 u3 h3N (by simp [hu3]) (by simp [hu3])
      have hX1 : (Function.update u1 .PAR 0) .X = n / 2 := by simp [hu1]
      refine ⟨_, ?_, (Eval.loop_true (by rw [isSomeB_hd, decide_eq_true_eq]; omega)
        (Eval.seq (Eval.seq (Eval.seq e1 e2) e3) e4) e5).of_eq ?_ rfl⟩
      · rw [hX1]
        omega
      · have hS : Function.update S1 (.inr .O)
            ((encodeNat (n / 2)).reverse.map Sym.bit ++ S1 (.inr .O)) =
            Function.update S0 (.inr .O) ((encodeNat n).reverse.map Sym.bit ++ S0 (.inr .O)) := by
          rw [hS1, Function.update_idem, Function.update_self, encodeNat_pos n hpos]
          simp
        have hu : Function.update u3 .NUM 0 = Function.update u .NUM 0 := by
          funext x
          cases x <;> simp [hu3, hu1, hX, hP]
        rw [hS, hu]

theorem toBin_ms (S0 : RK → List Sym) (u : RE → ℕ) (hX : u .X = 0) (hP : u .PAR = 0) :
    MS toBin S0 u (Function.update S0 (.inr .O)
      ((encodeNat (u .NUM)).reverse.map Sym.bit ++ S0 (.inr .O))) (Function.update u .NUM 0)
      (30 * u .NUM + 2) := by
  intro v
  have e0 := peekU_eval (a := .NUM) rfl v S0 u
  obtain ⟨t, ht, e1⟩ := toBin_loop (u .NUM) S0 u rfl hX hP
  exact ⟨none, 1 + t, by omega, Eval.seq e0 e1⟩

/-- Loop body of `countO`. -/
def countBody : SProg RK :=
  .seq (.seq (popR (.inr .O)) (pushC (.inr .Z) .mark)) (peekR (.inr .O))

/-- `Z += |O|`, `O := []`. -/
def countO : SProg RK := .seq (peekR (.inr .O)) (.loop isSomeB countBody)

theorem countO_loop : ∀ (l : List Sym) (S0 : RK → List Sym) (u : RE → ℕ), S0 (.inr .O) = l →
    Eval [] (.loop isSomeB countBody) ⟨l.head?, mkS S0 u⟩
      ⟨none, mkS (Function.update S0 (.inr .O) []) (Function.update u .Z (u .Z + l.length))⟩
      (4 * l.length + 1)
  | [], S0, u, hl => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ rfl
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    rw [List.length_nil, Nat.add_zero, Function.update_eq_self, ← hl, Function.update_eq_self]
  | a :: l, S0, u, hl => by
    have e1 := popO_eval (a :: l).head? S0 u
    rw [hl, List.tail_cons] at e1
    have e2 := pushU_eval (a := .Z) rfl (a :: l).head? (Function.update S0 (.inr .O) l) u
    have e3 := peekO_eval (a :: l).head? (Function.update S0 (.inr .O) l)
      (Function.update u .Z (u .Z + 1))
    rw [Function.update_self] at e3
    have ih := countO_loop l (Function.update S0 (.inr .O) l) (Function.update u .Z (u .Z + 1))
      (Function.update_self _ _ _)
    have hSa : Function.update (Function.update S0 (.inr .O) l) (.inr .O) [] =
        Function.update S0 (.inr .O) [] := Function.update_idem _ _ _
    have hua : Function.update (Function.update u .Z (u .Z + 1)) .Z
        ((Function.update u .Z (u .Z + 1)) .Z + l.length) =
        Function.update u .Z (u .Z + (a :: l).length) := by
      rw [Function.update_self, Function.update_idem, List.length_cons]
      congr 1
      omega
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) e3) ih).of_eq
      (by rw [hSa, hua]) (by simp only [List.length_cons]; ring)

theorem countO_ms (S0 : RK → List Sym) (u : RE → ℕ) :
    MS countO S0 u (Function.update S0 (.inr .O) [])
      (Function.update u .Z (u .Z + (S0 (.inr .O)).length)) (4 * (S0 (.inr .O)).length + 2) := by
  intro v
  have e0 := peekO_eval v S0 u
  exact ⟨none, _, le_refl _, (Eval.seq e0 (countO_loop _ S0 u rfl)).of_eq rfl (by ring)⟩

/-- Output conditions: the halving stacks are empty and the bit buffer is empty. -/
def OutOK (S0 : RK → List Sym) (u : RE → ℕ) : Prop :=
  u .X = 0 ∧ u .PAR = 0 ∧ S0 (.inr .O) = []

/-- `Z += bitLen NUM`, `NUM := 0`. -/
def bitLenU : SProg RK := .seq toBin countO

theorem bitLenU_ms (S0 : RK → List Sym) (u : RE → ℕ) (hok : OutOK S0 u) :
    MS bitLenU S0 u S0 (Function.update (Function.update u .NUM 0) .Z (u .Z + bitLen (u .NUM)))
      (34 * u .NUM + 4) := by
  obtain ⟨hX, hP, hO⟩ := hok
  have h := (toBin_ms S0 u hX hP).seq (countO_ms _ _)
  have hb := bitLen_le (u .NUM)
  refine (h.mono ?_).of_eq ?_ ?_
  · simp only [Function.update_self, hO, List.append_nil, List.length_map, List.length_reverse]
    unfold bitLen at hb
    omega
  · rw [Function.update_idem, ← hO, Function.update_eq_self]
  · simp [hO, bitLen]

theorem mvO_eval (tgt : PN) (v : Option Sym) (S0 : RK → List Sym) (u : RE → ℕ) :
    Eval [] (moveAll (.inr .O) (.inl tgt)) ⟨v, mkS S0 u⟩
      ⟨none, mkS (Function.update (Function.update S0 (.inr .O) []) (.inl tgt)
        ((S0 (.inr .O)).reverse ++ S0 (.inl tgt))) u⟩ (4 * (S0 (.inr .O)).length + 2) := by
  have e := moveAll_eval (src := (.inr .O : RK)) (dst := .inl tgt) (by simp) [] v _ (mkS S0 u)
    (mkS_N (e := .O) rfl S0 u)
  rw [mkS_inl, upd_mkS_N (e := .O) rfl, upd_mkS_inl] at e
  exact e

/-- Push the header field `natSyms NUM ++ [mark]` on the named stack `tgt`; `NUM := 0`. -/
def pushNat (tgt : PN) : SProg RK :=
  .seq (.seq (pushC (.inl tgt) .mark) toBin) (moveAll (.inr .O) (.inl tgt))

theorem pushNat_ms (tgt : PN) (S0 : RK → List Sym) (u : RE → ℕ) (hok : OutOK S0 u) :
    MS (pushNat tgt) S0 u (Function.update S0 (.inl tgt) (hdrSyms [u .NUM] ++ S0 (.inl tgt)))
      (Function.update u .NUM 0) (34 * u .NUM + 5) := by
  obtain ⟨hX, hP, hO⟩ := hok
  intro v
  have e0 := pushL_eval tgt .mark v S0 u
  set S1 := Function.update S0 (.inl tgt) (Sym.mark :: S0 (.inl tgt)) with hS1
  obtain ⟨r1, t1, ht1, e1⟩ := toBin_ms S1 u hX hP v
  set S2 := Function.update S1 (.inr .O)
    ((encodeNat (u .NUM)).reverse.map Sym.bit ++ S1 (.inr .O)) with hS2
  have e2 := mvO_eval tgt r1 S2 (Function.update u .NUM 0)
  have hl : (S2 (.inr .O)).length = bitLen (u .NUM) := by
    simp [hS2, hS1, hO, bitLen]
  have hb := bitLen_le (u .NUM)
  refine ⟨none, _, ?_, (Eval.seq (Eval.seq e0 e1) e2).of_eq ?_ rfl⟩
  · rw [hl]
    omega
  · congr 2
    funext k
    rcases k with a | e
    · by_cases ha : a = tgt
      · subst ha
        simp [hS2, hS1, hO, hdrSyms, natSyms]
      · simp [hS2, hS1, ha]
    · by_cases he : e = .O
      · subst he
        simp [hS2, hS1, hO]
      · simp [hS2, hS1, he]

theorem encodeNat_two_pow : ∀ a : ℕ, encodeNat (2 ^ a) = List.replicate a false ++ [true]
  | 0 => by
    have h := encodeNat_add_add_one 0
    simp only [Nat.add_zero, Nat.zero_add] at h
    rw [pow_zero, h, encodeNat_zero]
    rfl
  | a + 1 => by
    rw [pow_succ, show 2 ^ a * 2 = 2 ^ a + 2 ^ a by ring, encodeNat_add,
      if_neg (by rw [encodeNat_eq_nil_iff]; exact (Nat.two_pow_pos a).ne'), encodeNat_two_pow a]
    rfl

theorem hdrSyms_two_pow (a : ℕ) :
    hdrSyms [2 ^ a] = List.replicate a (Sym.bit false) ++ [Sym.bit true, Sym.mark] := by
  simp [hdrSyms, natSyms, encodeNat_two_pow, List.map_replicate]

/-- Loop body of `pushPow2`. -/
def p2Body (tgt : PN) : SProg RK :=
  .seq (.seq (popR (.inr .NUM)) (pushC (.inl tgt) (.bit false))) (peekR (.inr .NUM))

/-- Push the header field of `2 ^ NUM` on the named stack `tgt`; `NUM := 0`. -/
def pushPow2 (tgt : PN) : SProg RK :=
  .seq (.seq (.seq (pushC (.inl tgt) .mark) (pushC (.inl tgt) (.bit true))) (peekR (.inr .NUM)))
    (.loop isSomeB (p2Body tgt))

theorem p2_loop (tgt : PN) : ∀ (k : ℕ) (S0 : RK → List Sym) (u : RE → ℕ), u .NUM = k →
    Eval [] (.loop isSomeB (p2Body tgt)) ⟨(List.replicate k Sym.mark).head?, mkS S0 u⟩
      ⟨none, mkS (Function.update S0 (.inl tgt) (List.replicate k (Sym.bit false) ++
        S0 (.inl tgt))) (Function.update u .NUM 0)⟩ (4 * k + 1)
  | 0, S0, u, hk => by
    refine (Eval.loop_false (by rfl)).of_eq ?_ (by ring)
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    rw [List.replicate_zero, List.nil_append, Function.update_eq_self, ← hk,
      Function.update_eq_self]
  | k + 1, S0, u, hk => by
    have e1 := popU_eval (a := .NUM) rfl (List.replicate (k + 1) Sym.mark).head? S0 u
    rw [hk, Nat.add_sub_cancel] at e1
    have e2 := pushL_eval tgt (.bit false) (List.replicate (k + 1) Sym.mark).head? S0
      (Function.update u .NUM k)
    have e3 := peekU_eval (a := .NUM) rfl (List.replicate (k + 1) Sym.mark).head?
      (Function.update S0 (.inl tgt) (Sym.bit false :: S0 (.inl tgt))) (Function.update u .NUM k)
    rw [Function.update_self] at e3
    have ih := p2_loop tgt k (Function.update S0 (.inl tgt) (Sym.bit false :: S0 (.inl tgt)))
      (Function.update u .NUM k) (Function.update_self _ _ _)
    refine (Eval.loop_true (by rfl) (Eval.seq (Eval.seq e1 e2) e3) ih).of_eq ?_ (by ring)
    simp only [Function.update_idem, Function.update_self]
    rw [List.replicate_succ', List.append_assoc, List.singleton_append]

theorem pushPow2_ms (tgt : PN) (S0 : RK → List Sym) (u : RE → ℕ) :
    MS (pushPow2 tgt) S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [2 ^ u .NUM] ++ S0 (.inl tgt)))
      (Function.update u .NUM 0) (4 * u .NUM + 4) := by
  intro v
  have e0 := pushL_eval tgt .mark v S0 u
  set S1 := Function.update S0 (.inl tgt) (Sym.mark :: S0 (.inl tgt)) with hS1
  have e1 := pushL_eval tgt (.bit true) v S1 u
  set S2 := Function.update S1 (.inl tgt) (Sym.bit true :: S1 (.inl tgt)) with hS2
  have e2 := peekU_eval (a := .NUM) rfl v S2 u
  have e3 := p2_loop tgt (u .NUM) S2 u rfl
  refine ⟨none, _, le_of_eq (by ring), (Eval.seq (Eval.seq (Eval.seq e0 e1) e2) e3).of_eq ?_ rfl⟩
  rw [hS2, hS1, hdrSyms_two_pow]
  simp only [Function.update_idem, Function.update_self, List.append_assoc, List.cons_append,
    List.nil_append]

/-! ## Repeated fields -/

/-- Loop body of `rep P`: one call of `P` on a copy of `V`. -/
def repBody (P : SProg RK) : SProg RK :=
  .seq (.seq (.seq (popR (.inr .CNT)) (copyAll (.inr .V) (.inr .NUM) (.inr .T))) P)
    (peekR (.inr .CNT))

/-- `CNT` calls of the field pusher `P` on copies of `V`; `CNT := 0`. -/
def rep (P : SProg RK) : SProg RK := .seq (peekR (.inr .CNT)) (.loop isSomeB (repBody P))

theorem hdrSyms_replicate_succ (c x : ℕ) :
    hdrSyms (List.replicate (c + 1) x) = hdrSyms (List.replicate c x) ++ hdrSyms [x] := by
  rw [List.replicate_succ']
  simp [hdrSyms, List.flatMap_append]

theorem rep_loop (P : SProg RK) (tgt : PN) (y a Bp : ℕ)
    (hP : ∀ S0 u, OutOK S0 u → u .NUM = a → MS P S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt))) (Function.update u .NUM 0) Bp) :
    ∀ (c : ℕ) (S0 : RK → List Sym) (u : RE → ℕ), u .CNT = c → u .V = a → u .NUM = 0 →
      u .T = 0 → OutOK S0 u → ∃ t, t ≤ c * (Bp + 9 * a + 8) + 1 ∧
        Eval [] (.loop isSomeB (repBody P)) ⟨(List.replicate c Sym.mark).head?, mkS S0 u⟩
          ⟨none, mkS (Function.update S0 (.inl tgt) (hdrSyms (List.replicate c y) ++
            S0 (.inl tgt))) (Function.update u .CNT 0)⟩ t
  | 0, S0, u, hc, _, _, _, _ => by
    refine ⟨1, by omega, (Eval.loop_false (by rfl)).of_eq ?_ rfl⟩
    show (⟨none, mkS S0 u⟩ : SSt RK) = _
    simp only [List.replicate_zero, hdrSyms, List.flatMap_nil, List.nil_append,
      Function.update_eq_self]
    rw [← hc, Function.update_eq_self]
  | c + 1, S0, u, hc, hV, hN, hT, hok => by
    have e1 := popU_eval (a := .CNT) rfl (List.replicate (c + 1) Sym.mark).head? S0 u
    rw [hc, Nat.add_sub_cancel] at e1
    have e2 := cpU_eval (a := .V) (b := .NUM) (t := .T) rfl rfl rfl (by decide) (by decide)
      (by decide) (List.replicate (c + 1) Sym.mark).head? S0 (Function.update u .CNT c)
      (by simp [hT])
    set u2 := Function.update (Function.update u .CNT c) .NUM
      ((Function.update u .CNT c) .V + (Function.update u .CNT c) .NUM) with hu2
    have hok2 : OutOK S0 u2 := ⟨by simp [hu2, hok.1], by simp [hu2, hok.2.1], hok.2.2⟩
    obtain ⟨r3, t3, ht3, e3⟩ := hP S0 u2 hok2 (by simp [hu2, hV, hN]) none
    set S3 := Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt)) with hS3
    have e4 := peekU_eval (a := .CNT) rfl r3 S3 (Function.update u2 .NUM 0)
    have h4 : (Function.update u2 .NUM 0) .CNT = c := by simp [hu2]
    rw [h4] at e4
    obtain ⟨t5, ht5, e5⟩ := rep_loop P tgt y a Bp hP c S3 (Function.update u2 .NUM 0) h4
      (by simp [hu2, hV]) (by simp) (by simp [hu2, hT])
      ⟨by simp [hu2, hok.1], by simp [hu2, hok.2.1], by simp [hS3, hok.2.2]⟩
    have hVc : (Function.update u .CNT c) .V = a := by simp [hV]
    refine ⟨_, ?_, (Eval.loop_true (by rfl) (Eval.seq (Eval.seq (Eval.seq e1 e2) e3) e4)
      e5).of_eq ?_ rfl⟩
    · rw [hVc]
      nlinarith
    · have hS : Function.update S3 (.inl tgt) (hdrSyms (List.replicate c y) ++ S3 (.inl tgt)) =
          Function.update S0 (.inl tgt) (hdrSyms (List.replicate (c + 1) y) ++ S0 (.inl tgt)) := by
        rw [hS3, Function.update_idem, Function.update_self, hdrSyms_replicate_succ,
          List.append_assoc]
      have hu : Function.update (Function.update u2 .NUM 0) .CNT 0 = Function.update u .CNT 0 := by
        funext x
        cases x <;> simp [hu2, hN]
      rw [hS, hu]

theorem rep_ms (P : SProg RK) (tgt : PN) (y a Bp : ℕ)
    (hP : ∀ S0 u, OutOK S0 u → u .NUM = a → MS P S0 u
      (Function.update S0 (.inl tgt) (hdrSyms [y] ++ S0 (.inl tgt))) (Function.update u .NUM 0) Bp)
    (S0 : RK → List Sym) (u : RE → ℕ) (hV : u .V = a) (hN : u .NUM = 0) (hT : u .T = 0)
    (hok : OutOK S0 u) :
    MS (rep P) S0 u (Function.update S0 (.inl tgt) (hdrSyms (List.replicate (u .CNT) y) ++
      S0 (.inl tgt))) (Function.update u .CNT 0) (u .CNT * (Bp + 9 * a + 8) + 2) := by
  intro v
  have e0 := peekU_eval (a := .CNT) rfl v S0 u
  obtain ⟨t, ht, e1⟩ := rep_loop P tgt y a Bp hP (u .CNT) S0 u rfl hV hN hT hok
  exact ⟨none, 1 + t, by omega, Eval.seq e0 e1⟩

/-! ## Header arithmetic -/

section HdrMath

open SubNLogN.Math.Cost SubNLogN.Math.Bridge

theorem dK46 (K0 : ℕ) : dK row46 K0 = floorRatPow K0 1 15 := rfl

theorem KK46 (K0 : ℕ) : KK row46 K0 = floorRatPow (dK row46 K0) 1 (2 ^ 50) := rfl

theorem lK46 (K0 : ℕ) : lK row46 K0 = (K0 + dK row46 K0 - 1) / dK row46 K0 := rfl

theorem dK46_zero {K0 : ℕ} (h : dK row46 K0 = 0) : K0 = 0 := by
  by_contra hK
  have h1 := (le_floorRatPow_iff (x := K0) (e₁ := 1) (e₂ := 15) (by norm_num) 1).2
    (by rw [one_pow, pow_one]; omega)
  rw [← dK46, h] at h1
  omega

theorem dK46_le (K0 : ℕ) : dK row46 K0 ≤ K0 := frp_le K0 15 (by norm_num)

theorem KK46_le (K0 : ℕ) : KK row46 K0 ≤ dK row46 K0 := by
  rw [KK46]
  exact frp_le _ (2 ^ 50) (by positivity)

theorem dK46_pow (K0 : ℕ) : (dK row46 K0 + 1) ^ 15 ≤ 2 ^ 15 * K0 + 1 := by
  rw [dK46]
  have h1 : floorRatPow K0 1 15 ^ 15 ≤ K0 := by
    have := (le_floorRatPow_iff (x := K0) (e₁ := 1) (e₂ := 15) (by norm_num)
      (floorRatPow K0 1 15)).1 le_rfl
    rwa [pow_one] at this
  rcases Nat.eq_zero_or_pos (floorRatPow K0 1 15) with h0 | hpos
  · rw [h0]; norm_num
  · have h2 : (floorRatPow K0 1 15 + 1) ^ 15 ≤ (2 * floorRatPow K0 1 15) ^ 15 :=
      Nat.pow_le_pow_left (by omega) 15
    rw [mul_pow] at h2
    calc (floorRatPow K0 1 15 + 1) ^ 15 ≤ 2 ^ 15 * floorRatPow K0 1 15 ^ 15 := h2
      _ ≤ 2 ^ 15 * K0 := Nat.mul_le_mul_left _ h1
      _ ≤ 2 ^ 15 * K0 + 1 := Nat.le_succ _

theorem lK46_le (K0 : ℕ) : lK row46 K0 ≤ K0 := by
  rw [lK46]
  rcases Nat.eq_zero_or_pos (dK row46 K0) with h0 | hpos
  · rw [h0]; simp
  · apply Nat.div_le_of_le_mul
    have hK : 1 ≤ K0 := le_trans hpos (dK46_le K0)
    obtain ⟨d', hd'⟩ : ∃ d', dK row46 K0 = d' + 1 := ⟨dK row46 K0 - 1, by omega⟩
    obtain ⟨k', hk'⟩ : ∃ k', K0 = k' + 1 := ⟨K0 - 1, by omega⟩
    rw [hd']
    rw [hk']
    have h3 : k' + 1 + (d' + 1) - 1 = k' + d' + 1 := by omega
    rw [h3]
    nlinarith [Nat.zero_le (d' * k')]

theorem fnewM_le (K0 : ℕ) : dK row46 K0 * lK row46 K0 - K0 ≤ fnewD row46 K0 := by
  unfold fnewD
  rw [lK46]
  rcases Nat.eq_zero_or_pos (dK row46 K0) with h0 | hpos
  · rw [h0]; simp
  · have h1 := Nat.div_mul_le_self (K0 + dK row46 K0 - 1) (dK row46 K0)
    rw [Nat.mul_comm] at h1
    omega

theorem ofFn_fnewA (K0 : ℕ) :
    List.ofFn (fnewA row46 K0) =
      List.replicate (dK row46 K0 * lK row46 K0 - K0) (lK row46 K0 - 1) ++
        List.replicate (fnewD row46 K0 - (dK row46 K0 * lK row46 K0 - K0)) (lK row46 K0) := by
  have hm := fnewM_le K0
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_replicate]
    omega
  · intro i h1 h2
    rw [List.getElem_ofFn]
    unfold fnewA
    split_ifs with hi
    · rw [List.getElem_append_left (by simpa using hi), List.getElem_replicate]
    · rw [List.getElem_append_right (by simp at hi ⊢; omega), List.getElem_replicate]

theorem ofFn_fnewShape (K0 : ℕ) :
    List.ofFn (fnewShape row46 K0) =
      (List.ofFn (fnewA row46 K0)).map (fun a => 2 ^ a) ++ [2 ^ fnewL row46 K0] := by
  rw [List.ofFn_succ_last, List.map_ofFn]
  congr 1
  · congr 1
    funext i
    simp [fnewShape, Function.comp, i.isLt]
  · simp [fnewShape]

theorem hdrSyms_append (l1 l2 : List ℕ) : hdrSyms (l1 ++ l2) = hdrSyms l1 ++ hdrSyms l2 := by
  simp [hdrSyms, List.flatMap_append]

theorem hdrSyms_cons (x : ℕ) (l : List ℕ) : hdrSyms (x :: l) = hdrSyms [x] ++ hdrSyms l := by
  simp [hdrSyms]

theorem clog_eq_bitLen (x : ℕ) (hx : 1 ≤ x) : Nat.clog 2 x = bitLen (x - 1) := by
  apply le_antisymm
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    have := IntMulTM.lt_two_pow_length_encodeNat (x - 1)
    unfold bitLen
    omega
  · unfold bitLen
    rw [IntMulTM.length_encodeNat, Nat.size_le]
    have := Nat.le_pow_clog (b := 2) (by norm_num) x
    omega

end HdrMath

/-! ## Named stacks and bit buffers inside the unary calculus -/

/-- Stacks stored in the `S0` component of `mkS` (named stacks and the bit buffers). -/
def IsN : RK → Prop
  | .inl _ => True
  | .inr e => isU e = false

theorem mkS_isN {k : RK} (h : IsN k) (S0 : RK → List Sym) (u : RE → ℕ) : mkS S0 u k = S0 k := by
  rcases k with a | e
  · rfl
  · exact mkS_N h S0 u

theorem upd_mkS_isN {k : RK} (h : IsN k) (S0 : RK → List Sym) (u : RE → ℕ) (l : List Sym) :
    Function.update (mkS S0 u) k l = mkS (Function.update S0 k l) u := by
  rcases k with a | e
  · exact upd_mkS_inl S0 u a l
  · exact upd_mkS_N h S0 u l

theorem moveBlock_ms {a b : RK} (ha : IsN a) (hb : IsN b) (hab : a ≠ b) (es : List Bool)
    (rest : List Sym) (hrest : TermOK rest) (S0 : RK → List Sym) (u : RE → ℕ)
    (hS : S0 a = es.map Sym.bit ++ rest) :
    MS (moveBlock a b) S0 u (Function.update (Function.update S0 a rest) b
      (es.reverse.map Sym.bit ++ S0 b)) u (3 * es.length + 4) := by
  intro v
  have e := moveBlock_eval hab [] v es rest (mkS S0 u) hrest (by rw [mkS_isN ha, hS])
  rw [mkS_isN hb, upd_mkS_isN ha, upd_mkS_isN hb] at e
  exact ⟨_, _, le_refl _, e⟩

/-- Move the top symbol of `a` onto `b`. -/
def movTop (a b : RK) : SProg RK := .seq (popR a) (pushR b)

theorem movTop_ms {a b : RK} (ha : IsN a) (hb : IsN b) (hab : a ≠ b) (x : Sym) (rest : List Sym)
    (S0 : RK → List Sym) (u : RE → ℕ) (hS : S0 a = x :: rest) :
    MS (movTop a b) S0 u (Function.update (Function.update S0 a rest) b (x :: S0 b)) u 2 := by
  intro v
  have e1 := Eval.pop [] a (fun _ o => o) v (mkS S0 u)
  rw [mkS_isN ha, hS, upd_mkS_isN ha] at e1
  have e2 := Eval.push [] b (fun r => r.getD .sep) (x :: rest).head?
    (mkS (Function.update S0 a (x :: rest).tail) u)
  rw [mkS_isN hb, upd_mkS_isN hb] at e2
  refine ⟨(x :: rest).head?, 2, le_refl _, (Eval.seq e1 e2).of_eq ?_ rfl⟩
  simp [Function.update_of_ne (Ne.symm hab)]

/-! ## Reading the header fields -/

/-- Convert the top header field of the named stack `src` into the unary register `dst`
(through `H`, `T`); `src` restored. -/
def fieldTo (src : PN) (dst : RE) : SProg RK :=
  .seq (moveBlock (.inl src) (.inr .H)) (horner (.inl src) (.inr dst) (.inr .T) (.inr .H))

/-- Cost of `fieldTo` on the field `natSyms n`. -/
def fcost (n : ℕ) : ℕ := 3 * bitLen n + 4 + (hcost 0 (encodeNat n).reverse + 1)

theorem fcost_le (n : ℕ) : fcost n ≤ 13 * n + 16 * bitLen n + 6 := by
  have h := hcost_le 0 (encodeNat n).reverse
  rw [hval_encodeNat, List.length_reverse] at h
  unfold fcost bitLen
  omega

theorem fieldTo_ms (src : PN) {dst : RE} (hd : isU dst = true) (hdT : dst ≠ .T) (n : ℕ)
    (R : List Sym) (S0 : RK → List Sym) (u : RE → ℕ)
    (hS : S0 (.inl src) = natSyms n ++ Sym.mark :: R) (hH : S0 (.inr .H) = [])
    (hu : u dst = 0) (hT : u .T = 0) :
    MS (fieldTo src dst) S0 u S0 (Function.update u dst n) (fcost n) := by
  intro v
  have hdH : dst ≠ .H := by rintro rfl; simp [isU] at hd
  have e1 := moveBlock_eval (src := (.inl src : RK)) (dst := .inr .H) (by simp) [] v
    (encodeNat n) (Sym.mark :: R) (mkS S0 u) (TermOK.cons rfl R) (by rw [mkS_inl, hS]; rfl)
  rw [mkS_N (e := .H) rfl, hH, List.append_nil, upd_mkS_inl, upd_mkS_N (e := .H) rfl] at e1
  set S1 := Function.update (Function.update S0 (.inl src) (Sym.mark :: R)) (.inr .H)
    ((encodeNat n).reverse.map Sym.bit) with hS1
  have e2 := horner_eval (src := (.inl src : RK)) (acc := .inr dst) (acc2 := .inr .T)
    (h := .inr .H) (by simp) (by simp) (by simp) (by simpa using hdT) (by simpa using hdH)
    (by simp) [] (Sym.mark :: R).head? (encodeNat n).reverse 0 (mkS S1 u)
    (by rw [mkS_N (e := .H) rfl]; simp [hS1]) (by rw [mkS_U hd, hu])
    (by rw [mkS_U rfl, hT]; rfl)
  rw [hval_encodeNat, List.reverse_reverse, upd_mkS_N (e := .H) rfl, mkS_inl, upd_mkS_inl,
    upd_mkS_U hd] at e2
  refine ⟨none, _, le_refl _, (Eval.seq e1 e2).of_eq ?_ (by unfold fcost bitLen; ring)⟩
  congr 2
  funext k
  rcases k with a | e
  · by_cases ha : a = src
    · subst ha; simp [hS1, hS, natSyms]
    · simp [hS1, ha]
  · by_cases he : e = .H
    · subst he; simp [hS1, hH]
    · simp [hS1, he]

/-- **Read the header**: `B := b`, `K := K0` (from `C0`), `I := p_in` (from `C1`); `C0`, `C1`
restored (the `b` field is parked on `G` while `K0` is read). -/
def readProg : SProg RK :=
  .seq (.seq (.seq (.seq (.seq (.seq (fieldTo .C0 .B) (moveBlock (.inl .C0) (.inr .G)))
    (movTop (.inl .C0) (.inr .G))) (fieldTo .C0 .K)) (movTop (.inr .G) (.inl .C0)))
    (moveBlock (.inr .G) (.inl .C0))) (fieldTo .C1 .I)

theorem read_ms (b K0 pin : ℕ) (R0 R1 : List Sym) (S0 : RK → List Sym) (u : RE → ℕ)
    (hC0 : S0 (.inl .C0) = natSyms b ++ Sym.mark :: (natSyms K0 ++ Sym.mark :: R0))
    (hC1 : S0 (.inl .C1) = natSyms pin ++ Sym.mark :: R1)
    (hH : S0 (.inr .H) = []) (hG : S0 (.inr .G) = []) (hB : u .B = 0) (hK : u .K = 0)
    (hI : u .I = 0) (hT : u .T = 0) :
    MS readProg S0 u S0 (Function.update (Function.update (Function.update u .B b) .K K0) .I pin)
      (fcost b + fcost K0 + fcost pin + 6 * bitLen b + 12) := by
  have h1 := fieldTo_ms .C0 (dst := .B) rfl (by decide) b _ S0 u hC0 hH hB hT
  set u1 := Function.update u .B b with hu1
  have h2 := moveBlock_ms (a := .inl .C0) (b := .inr .G) trivial rfl (by simp) (encodeNat b) _
    (TermOK.cons rfl _) S0 u1 hC0
  set S2 := Function.update (Function.update S0 (.inl .C0)
    (Sym.mark :: (natSyms K0 ++ Sym.mark :: R0))) (.inr .G)
    ((encodeNat b).reverse.map Sym.bit ++ S0 (.inr .G)) with hS2
  have h3 := movTop_ms (a := .inl .C0) (b := .inr .G) trivial rfl (by simp) .mark
    (natSyms K0 ++ Sym.mark :: R0) S2 u1 (by simp [hS2])
  set S3 := Function.update (Function.update S2 (.inl .C0) (natSyms K0 ++ Sym.mark :: R0))
    (.inr .G) (Sym.mark :: S2 (.inr .G)) with hS3
  have h4 := fieldTo_ms .C0 (dst := .K) rfl (by decide) K0 R0 S3 u1 (by simp [hS3])
    (by simp [hS3, hS2, hH]) (by simp [hu1, hK]) (by simp [hu1, hT])
  set u4 := Function.update u1 .K K0 with hu4
  have h5 := movTop_ms (a := .inr .G) (b := .inl .C0) rfl trivial (by simp) .mark (S2 (.inr .G))
    S3 u4 (by simp [hS3])
  set S5 := Function.update (Function.update S3 (.inr .G) (S2 (.inr .G))) (.inl .C0)
    (Sym.mark :: S3 (.inl .C0)) with hS5
  have h6 := moveBlock_ms (a := .inr .G) (b := .inl .C0) rfl trivial (by simp)
    (encodeNat b).reverse [] TermOK.nil S5 u4 (by simp [hS5, hS3, hS2, hG])
  set S6 := Function.update (Function.update S5 (.inr .G) []) (.inl .C0)
    ((encodeNat b).reverse.reverse.map Sym.bit ++ S5 (.inl .C0)) with hS6
  have hS6eq : S6 = S0 := by
    funext k
    rcases k with a | e
    · by_cases ha : a = .C0
      · subst ha; simp [hS6, hS5, hS3, hS2, hC0, natSyms]
      · simp [hS6, hS5, hS3, hS2, ha]
    · by_cases he : e = .G
      · subst he; simp [hS6, hS5, hS3, hS2, hG]
      · simp [hS6, hS5, hS3, hS2, he]
  have h7 := fieldTo_ms .C1 (dst := .I) rfl (by decide) pin R1 S6 u4 (by rw [hS6eq]; exact hC1)
    (by rw [hS6eq]; exact hH) (by simp [hu4, hu1, hI]) (by simp [hu4, hu1, hT])
  have h := (((((h1.seq h2).seq h3).seq h4).seq h5).seq h6).seq h7
  refine (h.mono (le_of_eq ?_)).of_eq hS6eq rfl
  simp only [List.length_reverse]
  unfold bitLen
  ring

end SubNLogN.Machine.Pipe.ReadParamsAux
