import WP.W9s.Count
import WP.W9s.Layout

/-!
# WP.W9s.ConvU — unary doubling and header-bit loops (helpers of piece [c])

All names live in `WP.W9s.Conv`.
* `rwc K src dst g`: `rewindTo` through the symbol register.
* `dbl K k`: double the unary counter on `k` in place, through the guarded `sT2` (`9n + 4` steps).
* `mvF K`: move one header field (bits, then `mark`) from `sC0` onto `sTC`.
* Loops over the leading `0` bits of a header field on `sC0` (each bit goes to `sTC`):
  `cntFBody` counts them on `sV`; `dblFBody` counts them on `sV'` and doubles `sUR`.
* `dblUBody`: for each unit of `sV'`, double `sDS`.
-/

namespace WP.W9s

open TMFw TMFw.Lib TMFw.Contracts TMFw.Contracts.W9 WP.W7k2 IntMul

namespace Conv

/-- `rewindTo` through the symbol register. -/
def rwc (K : Kit) (src dst : Host) (g : Sym) : MProg K :=
  (WP.W9comp.rewindTo src dst g).liftRegs (lS K)

theorem rwc_closed (K : Kit) (src dst : Host) (g : Sym) : (rwc K src dst g).Closed :=
  WP.W9comp.closed_rewind _ _ _ _

/-! ## Unary doubling -/

/-- One unit off `src`, two units onto `dst`. -/
def dblBody (K : Kit) (src dst : Host) : MProg K :=
  .seq (popS src) (.seq (pushS dst symU) (pushS dst symU))

theorem units_dbl (n : ℕ) (L : List Sym) :
    units (2 * n) ++ symU :: symU :: L = units (2 * (n + 1)) ++ L := by
  rw [show 2 * (n + 1) = 2 * n + 2 by ring, units_add, List.append_assoc]
  rfl

theorem LoopHT.dbl (K : Kit) {src dst : Host} (hne : src ≠ dst) (rest : List Sym)
    (hr : rest.head? ≠ some symU) (ρ : List (MProg K)) :
    ∀ (n : ℕ) (B : Host → List Sym), B src = units n ++ rest →
      LoopHT ρ (lS K) src isU (dblBody K src dst) B
        (Function.update (Function.update B src rest) dst (units (2 * n) ++ B dst)) (5 * n + 1)
  | 0, B, hB => by
    have hB' : B src = rest := hB
    refine Triple.post (LoopHT.stop (by simp [isU, hB', hr])) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = src
    · subst hx
      simp [hB', hne]
    · by_cases hx' : x = dst
      · subst hx'
        simp [units]
      · simp [hx, hx']
  | n + 1, B, hB => by
    have h := LoopHT.step (by simp [isU, hB, units_succ])
      ((HT.popS (σ := K.R) src B symU (units n ++ rest) (by rw [hB]; rfl) ρ).seq
        ((HT.pushS (σ := K.R) dst symU _ ρ).seq (HT.pushS (σ := K.R) dst symU _ ρ)))
      (LoopHT.dbl K hne rest hr ρ n _ (by simp [hne]))
    refine Triple.post (h.mono (by omega)) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases hx : x = dst
    · subst hx
      simp [Ne.symm hne, units_dbl]
    · by_cases hx' : x = src
      · subst hx'
        simp [hne]
      · simp [hx, hx']

/-- Double the unary counter on `k` (through `sT2`, which holds a guard on top). -/
def dbl (K : Kit) (k : Host) : MProg K :=
  .seq (uMove (lS K) k sT2) (whileTop (lS K) sT2 isU (dblBody K sT2 k))

theorem dbl_closed (K : Kit) (k : Host) : (dbl K k).Closed :=
  ⟨uMove_closed _ _ _, whileTop_closed _ _ _ ⟨trivial, trivial, trivial⟩⟩

theorem HT.dbl (K : Kit) {k : Host} (hk : k ≠ sT2) (n : ℕ) (rk T2r : List Sym)
    (hrk : rk.head? ≠ some symU) (B : Host → List Sym) (hB : B k = units n ++ rk)
    (hT2 : B sT2 = symG :: T2r) (ρ : List (MProg K)) :
    HT ρ B (dbl K k) (Function.update B k (units (2 * n) ++ rk)) (9 * n + 4) := by
  have chain :=
    (HT.uMove (lS K) (src := k) (dst := sT2) hk n rk hrk B hB ρ).seq <|
    HT.whileTop (LoopHT.dbl K (src := sT2) (dst := k) (Ne.symm hk) (symG :: T2r)
      (by simp [symG, symU]) ρ n _ (by simp [hT2]))
  refine chain.of_eq ?_ (by omega)
  funext x
  by_cases h1 : x = k
  · subst h1
    simp [hk]
  by_cases h2 : x = sT2
  · subst h2
    simp [hT2, Ne.symm hk]
  simp [h1, h2]

/-! ## Header fields and their leading zeros -/

/-- Move one header field (its bits and its `mark`) from `sC0` onto `sTC`. -/
def mvF (K : Kit) : MProg K := .seq (rwc K sC0 sTC Sym.mark) (pushS sTC Sym.mark)

theorem mvF_closed (K : Kit) : (mvF K).Closed := ⟨rwc_closed _ _ _ _, trivial⟩

theorem HT.mvF (K : Kit) (L rest : List Sym) (hL : Sym.mark ∉ L) (B : Host → List Sym)
    (hB : B sC0 = L ++ Sym.mark :: rest) (ρ : List (MProg K)) :
    HT ρ B (mvF K) (Function.update (Function.update B sC0 rest) sTC
      (Sym.mark :: (L.reverse ++ B sTC))) (3 * L.length + 3) := by
  have chain :=
    (HT.rewind (lS K) (src := sC0) (dst := sTC) (by decide) Sym.mark L rest B hL hB ρ).seq
      (HT.pushS sTC Sym.mark _ ρ)
  refine chain.of_eq ?_ (by omega)
  funext x
  by_cases h1 : x = sTC
  · subst h1
    simp
  simp [h1]

/-- Is the peeked symbol the bit `0`? -/
def isF (o : Option Sym) : Bool := decide (o = some (Sym.bit false))

theorem rep_F (k : ℕ) (L : List Sym) :
    List.replicate k (Sym.bit false) ++ Sym.bit false :: L =
      List.replicate (k + 1) (Sym.bit false) ++ L := by
  rw [List.replicate_succ', List.append_assoc, List.singleton_append]

/-- Move a leading `0` from `sC0` to `sTC` and count it on `sV`. -/
def cntFBody (K : Kit) : MProg K :=
  .seq (popS sC0) (.seq (pushS sTC (Sym.bit false)) (pushS sV symU))

theorem LoopHT.cntF (K : Kit) (rest : List Sym) (ρ : List (MProg K)) :
    ∀ (k : ℕ) (B : Host → List Sym),
      B sC0 = List.replicate k (Sym.bit false) ++ Sym.bit true :: rest →
      LoopHT ρ (lS K) sC0 isF (cntFBody K) B
        (Function.update (Function.update (Function.update B sC0 (Sym.bit true :: rest)) sTC
          (List.replicate k (Sym.bit false) ++ B sTC)) sV (units k ++ B sV))
        (5 * k + 1)
  | 0, B, hB => by
    have hB' : B sC0 = Sym.bit true :: rest := hB
    refine Triple.post (LoopHT.stop (by simp [isF, hB'])) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases h1 : x = sC0
    · subst h1
      simp [hB']
    by_cases h2 : x = sTC
    · subst h2
      simp
    by_cases h3 : x = sV
    · subst h3
      simp [units]
    simp [h1, h2, h3]
  | k + 1, B, hB => by
    have h := LoopHT.step (by simp [isF, hB, List.replicate_succ])
      ((HT.popS (σ := K.R) sC0 B (Sym.bit false)
          (List.replicate k (Sym.bit false) ++ Sym.bit true :: rest)
          (by rw [hB, List.replicate_succ]; rfl) ρ).seq
        ((HT.pushS (σ := K.R) sTC (Sym.bit false) _ ρ).seq (HT.pushS (σ := K.R) sV symU _ ρ)))
      (LoopHT.cntF K rest ρ k _ (by simp))
    refine Triple.post (h.mono (by omega)) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases h1 : x = sC0
    · subst h1
      simp
    by_cases h2 : x = sTC
    · subst h2
      simp [rep_F]
    by_cases h3 : x = sV
    · subst h3
      simp [units_append_cons]
    simp [h1, h2, h3]

/-- Move a leading `0` from `sC0` to `sTC`, count it on `sV'`, double `sUR`. -/
def dblFBody (K : Kit) : MProg K :=
  .seq (popS sC0) (.seq (pushS sTC (Sym.bit false)) (.seq (pushS sV' symU) (dbl K sUR)))

/-- Cost of the `dblFBody` loop from `n` units with `k` zeros left. -/
def costF : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => 9 * n + 9 + costF (2 * n) k

theorem costF_le : ∀ k n : ℕ, costF n k + 9 * n ≤ 9 * (n * 2 ^ k) + 9 * k + 1
  | 0, n => by
    simp only [costF, pow_zero, Nat.mul_one]
    omega
  | k + 1, n => by
    have ih := costF_le k (2 * n)
    have e1 : 2 * n * 2 ^ k = n * 2 ^ (k + 1) := by ring
    rw [e1] at ih
    simp only [costF]
    omega

theorem LoopHT.dblF (K : Kit) (rest rUR T2r : List Sym) (ρ : List (MProg K)) :
    ∀ (k n : ℕ) (B : Host → List Sym),
      B sC0 = List.replicate k (Sym.bit false) ++ Sym.bit true :: rest →
      B sUR = units n ++ symG :: rUR → B sT2 = symG :: T2r →
      LoopHT ρ (lS K) sC0 isF (dblFBody K) B
        (Function.update (Function.update (Function.update (Function.update B sC0
          (Sym.bit true :: rest)) sTC (List.replicate k (Sym.bit false) ++ B sTC)) sV'
          (units k ++ B sV')) sUR (units (n * 2 ^ k) ++ symG :: rUR))
        (costF n k)
  | 0, n, B, hB, hUR, _ => by
    have hB' : B sC0 = Sym.bit true :: rest := hB
    refine Triple.post (LoopHT.stop (by simp [isF, hB'])) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases h1 : x = sC0
    · subst h1
      simp [hB']
    by_cases h2 : x = sTC
    · subst h2
      simp
    by_cases h3 : x = sV'
    · subst h3
      simp [units]
    by_cases h4 : x = sUR
    · subst h4
      simp [hUR]
    simp [h1, h2, h3, h4]
  | k + 1, n, B, hB, hUR, hT2 => by
    have h := LoopHT.step (by simp [isF, hB, List.replicate_succ])
      ((HT.popS (σ := K.R) sC0 B (Sym.bit false)
          (List.replicate k (Sym.bit false) ++ Sym.bit true :: rest)
          (by rw [hB, List.replicate_succ]; rfl) ρ).seq <|
        (HT.pushS (σ := K.R) sTC (Sym.bit false) _ ρ).seq <|
        (HT.pushS (σ := K.R) sV' symU _ ρ).seq <|
        HT.dbl K (k := sUR) (by decide) n (symG :: rUR) T2r (by simp [symG, symU]) _
          (by simp [hUR]) (by simp [hT2]) ρ)
      (LoopHT.dblF K rest rUR T2r ρ k (2 * n) _ (by simp) (by simp) (by simp [hT2]))
    refine Triple.post (h.mono (by simp only [costF]; omega)) (fun s hs => ?_)
    have e : units (2 * n * 2 ^ k) = units (n * 2 ^ (k + 1)) := by
      rw [show 2 * n * 2 ^ k = n * 2 ^ (k + 1) by ring]
    rw [hs]
    funext x
    by_cases h1 : x = sC0
    · subst h1
      simp
    by_cases h2 : x = sTC
    · subst h2
      simp [rep_F]
    by_cases h3 : x = sV'
    · subst h3
      simp [units_append_cons]
    by_cases h4 : x = sUR
    · subst h4
      simp [e]
    simp [h1, h2, h3, h4]

/-- Drop a unit of `sV'` and double `sDS`. -/
def dblUBody (K : Kit) : MProg K := .seq (popS sV') (dbl K sDS)

/-- Cost of the `dblUBody` loop from `n` units with `j` units of `sV'` left. -/
def costU : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, j + 1 => 9 * n + 7 + costU (2 * n) j

theorem costU_le : ∀ j n : ℕ, costU n j + 9 * n ≤ 9 * (n * 2 ^ j) + 7 * j + 1
  | 0, n => by
    simp only [costU, pow_zero, Nat.mul_one]
    omega
  | j + 1, n => by
    have ih := costU_le j (2 * n)
    have e1 : 2 * n * 2 ^ j = n * 2 ^ (j + 1) := by ring
    rw [e1] at ih
    simp only [costU]
    omega

theorem LoopHT.dblU (K : Kit) (rV rDS T2r : List Sym) (hrV : rV.head? ≠ some symU)
    (ρ : List (MProg K)) :
    ∀ (j n : ℕ) (B : Host → List Sym), B sV' = units j ++ rV →
      B sDS = units n ++ symG :: rDS → B sT2 = symG :: T2r →
      LoopHT ρ (lS K) sV' isU (dblUBody K) B
        (Function.update (Function.update B sV' rV) sDS (units (n * 2 ^ j) ++ symG :: rDS))
        (costU n j)
  | 0, n, B, hV, hDS, _ => by
    have hV' : B sV' = rV := hV
    refine Triple.post (LoopHT.stop (by simp [isU, hV', hrV])) (fun s hs => ?_)
    rw [hs]
    funext x
    by_cases h1 : x = sV'
    · subst h1
      simp [hV']
    by_cases h2 : x = sDS
    · subst h2
      simp [hDS]
    simp [h1, h2]
  | j + 1, n, B, hV, hDS, hT2 => by
    have h := LoopHT.step (by simp [isU, hV, units_succ])
      ((HT.popS (σ := K.R) sV' B symU (units j ++ rV) (by rw [hV]; rfl) ρ).seq <|
        HT.dbl K (k := sDS) (by decide) n (symG :: rDS) T2r (by simp [symG, symU]) _
          (by simp [hDS]) (by simp [hT2]) ρ)
      (LoopHT.dblU K rV rDS T2r hrV ρ j (2 * n) _ (by simp) (by simp) (by simp [hT2]))
    refine Triple.post (h.mono (by simp only [costU]; omega)) (fun s hs => ?_)
    have e : units (2 * n * 2 ^ j) = units (n * 2 ^ (j + 1)) := by
      rw [show 2 * n * 2 ^ j = n * 2 ^ (j + 1) by ring]
    rw [hs]
    funext x
    by_cases h1 : x = sV'
    · subst h1
      simp
    by_cases h2 : x = sDS
    · subst h2
      simp [e]
    simp [h1, h2]

#assert_std_axioms rwc_closed units_dbl LoopHT.dbl dbl_closed HT.dbl mvF_closed HT.mvF rep_F
  LoopHT.cntF costF_le LoopHT.dblF costU_le LoopHT.dblU

end Conv

end WP.W9s
