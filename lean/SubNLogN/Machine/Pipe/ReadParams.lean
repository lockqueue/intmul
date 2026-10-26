import SubNLogN.Machine.Pipe.ReadParamsMain
import SubNLogN.Machine.FFT.MidData

/-!
# Read-parameters kernel at the pipe's middle data (`readParams_holds`)

`readParams_holds p P₀ P₁ J : ReadParamsStmt fnewSched (walshMidData fnewSched p P₀ P₁ J)
readParamsCost`, from `readParams_holds_of`: the middle header of `walshMidData` is
`midList p0 K0` by definition (it depends on neither `p`, `P₀`, `P₁`, `J` nor `p_in`).
-/

namespace SubNLogN.Machine.Pipe

open SubNLogN.Machine ReadParamsAux

/-- **The read-parameters kernel at the pipe's data (`readParams_holds`)**, uniformly in the
layer parameters `p` and the constants `P₀ P₁ J` of the Walsh middle. -/
theorem readParams_holds (p : LayerParams) (P₀ P₁ J : ℕ) :
    ReadParamsStmt fnewSched (walshMidData fnewSched p P₀ P₁ J) readParamsCost :=
  readParams_holds_of _ (fun _ _ _ => rfl)

end SubNLogN.Machine.Pipe
