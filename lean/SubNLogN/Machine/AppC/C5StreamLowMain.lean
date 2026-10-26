import SubNLogN.Machine.AppC.C5StreamLowId
import SubNLogN.Machine.AppC.C5StreamLowCoef
import SubNLogN.Machine.AppC.C5StreamLowStream

/-!
# `LowShiftStmt`: the machine realization of `lowShift` (Proposition A.7 streams)

`StreamAux.lowShift_holds q m : LowShiftStmt q m`: for `2 ≤ q`, valid coefficients (denominators
prime to `q`) and `k, G, B ≥ 1`, the stream map of `lowShift X i c` equals the composite address map
`lowShiftMap` (`X_i ← D·X_i`, the K4 blocks `X_i ← X_i ∓ a_j X_j`, `X_i ← X_i/D`). The identity
holds for every index `y`, so the range hypothesis of the statement is not used. (Note: `Machine/AppC` and `C5`/`c5` retain earlier draft numbering for identifier stability; see Appendix A (`app:parameter-transfer`), Proposition A.7 (`prop:transfer11`).)

Both sides replace the radix-`Q` digit of `X_i` (place value `s = sX q m X i k G B`, `Q = q^(m^(k-1))`)
and keep every other digit:
* `streamMap` (`streamMap_lowShift_repl`, `C5StreamLowStream.lean`): new digit
  `t − Σ_{j<i} [c_j]_Q X_j`;
* `lowShiftMap` (`lowShiftMap_eq`, `C5StreamLowId.lean`): new digit `(t·D − Σ_{j<i} a_j X'_j)·D⁻¹`,
  where `X'_j` is read at the place value `s·Q·n1Low`, which is the place value of `X_j`
  (`place_eq`);
* the two agree by `lowCoef_identity` (`C5StreamLowCoef.lean`), since `D` is prime to `q`.
-/

namespace SubNLogN.Machine.C5.StreamAux

open TMFw TMFw.Contracts SubNLogN.Machine SubNLogN.Machine.C5
open SubNLogN.Machine.C5.UnitIdAux SubNLogN.Machine.C5.LowAux

/-- **`LowShiftStmt` holds** (for every `q, m`): under `2 ≤ q`, coefficients with denominators prime
to `q`, and `k, G, B ≥ 1`, `streamMap q m (.lowShift X i c) k N1 G B y = lowShiftMap q m X i c k G B y`
for every `y`. -/
theorem lowShift_holds (q m : ℕ) : LowShiftStmt q m := by
  intro hq X i c hc k Rt N1 G B y hk _ _ hG hB _
  have : NeZero (q ^ bOf m k) := ⟨pow_ne_zero _ (by omega)⟩
  have hs : 0 < sX q m X i k G B := LowAux.sX_pos (by omega) X i k hG hB
  rw [UnitIdAux.streamMap_lowShift_repl hq hk hG hB X i c y,
    LowAux.lowShiftMap_eq X i k G B hs c y]
  refine congrArg
    (fun u : ZMod (q ^ bOf m k) => repl (sX q m X i k G B) (q ^ bOf m k) y u.val) ?_
  have hlist : (((List.finRange m).filter (fun j => j < i)).map fun j =>
      (lowCoef c i j : ZMod (q ^ bOf m k)) *
        zd (q ^ bOf m k) (sX q m X i k G B * q ^ bOf m k * n1Low q m i j k) y) =
      (((List.finRange m).filter (fun j => j < i)).map fun j =>
        (lowCoef c i j : ZMod (q ^ bOf m k)) * zd (q ^ bOf m k) (sX q m X j k G B) y) := by
    refine List.map_congr_left fun j hj => ?_
    have hji : (j : ℕ) < (i : ℕ) := by simpa using (List.mem_filter.mp hj).2
    simp only [LowAux.place_eq X hji i.isLt k G B]
  rw [hlist]
  exact (LowCoefAux.lowCoef_identity c i (fun j => Nat.Coprime.pow_right _ (hc j))
    (zd (q ^ bOf m k) (sX q m X i k G B) y)
    (fun j => zd (q ^ bOf m k) (sX q m X j k G B) y)).symm

end SubNLogN.Machine.C5.StreamAux
