import WP.W7k2.Concrete
import WP.F9.Run

/-!
# Pre-check of the concrete builder at `L = 0`

The six external W7 sub-kernels are replaced by **test-only no-op placeholders** (`dummyI`); at `L = 0`
only the leaf part runs, so tap / c0c1 are never called (stdChar, pi, ln are the real
instances). Checks the init / levels / leaf / final path and the expected tape `tapeFromC 0 L p K`.
-/

namespace WP.W7k2.ConcreteBuildRunPre

open TMFw TMFw.Contracts WP.W7k2 WP.W7k2.Concrete

/-- TEST-ONLY placeholder: a closed no-op (never called at `L = 0`). -/
def dummyI (n : ℕ) : Inst n 16 Unit :=
  ⟨0, Unit, fun _ => (), .load id, by decide, inferInstance, ⟨()⟩, trivial⟩

def BIt : BI := BICof2 (dummyI 8) (dummyI 5)

def r0t : BIt.R := r0Of2 (dummyI 8) (dummyI 5) () ()

/-- All stacks of the builder. -/
def keys : List BL := (List.finRange 4).map Sum.inl ++ (List.finRange 32).map Sum.inr

/-- Junk tails (they start with a tag, so the input rests are `TermOK`). -/
def junk : List Sym := [.tag 9, .bit true]

/-- Inputs `L p K` on `1 2 3`, junk everywhere (also on `TR` and every scratch stack). -/
def st0 (L p K : ℕ) : BL → List Sym := fun k =>
  if k = .inl 1 then natSyms L ++ junk
  else if k = .inl 2 then natSyms p ++ junk
  else if k = .inl 3 then natSyms K ++ junk
  else junk

/-- One run: `(every stack as the contract says, steps)`. -/
def row (L p K : ℕ) : Bool × ℕ :=
  let S := st0 L p K
  let E := Function.update S (.inl 0) (tapeFromC 0 L p K ++ S (.inl 0))
  match WP.F9.runTabled (buildProg BIt) r0t keys ⟨r0t, S⟩ 10000000 with
  | none => (false, 0)
  | some (n, S') => (keys.all fun k => S' k == E k, n)

-- K = 1, 2 call stdChar at q = 2p+K+8 (series on ~25-bit precision): far beyond 60 s per run.
#eval [row 0 8 0]

end WP.W7k2.ConcreteBuildRunPre
