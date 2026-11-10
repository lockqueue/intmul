# Lean 4 development: integer multiplication below n log n (snapshot `b706618497aa`)

This archive contains the Lean 4 formalization described in Section 8 ("Formal verification in Lean 4") of the full paper
*A simpler algorithm for integer multiplication below n log n, with a formally verified proof* (2026).

It is a comment- and documentation-updated snapshot (`b706618497aa`, the first 12 hex digits of the SHA-256 of
`MANIFEST.sha256`) of the authors' development tree. The comment-stripped source of every library `.lean` file in this
archive (`2,011` library files total: `1,062` files / `299,120` lines in `SubNLogN/**`, and `949` files / `184,759` lines
across `IntMul`, `IntMulTM`, `WP`, `Contracts`, `LevelSync`, `IntMul.lean`, and `AxiomCheck.lean`) is recorded in
`MANIFEST_stripped.sha256`; running `python3 -B tools/check_semantic_freeze.py` in standalone mode inside this archive
re-verifies all `2,011` library `.lean` files against the recorded digests `MANIFEST_stripped.sha256` and
`SPEC_LOCK.sha256`.

License: Apache License 2.0 (see `LICENSE`).

## Main theorem

- `SubNLogN.Assembly.intMul_challenge : SubNLogN.Challenge.IntMulSubNLogN`, proved in
  `SubNLogN/Assembly/ChallengeHeadline.lean` (corresponding to Theorem 1 and Theorem 2 of the paper, at
  $\kappa = 2^{-46}$).
- The statement `IntMulSubNLogN`, the `Turing.TM2ComputableInTime` multi-stack Turing machine model, and the
  input/output encodings (`PairSym`, `encodeNatPair`, `encNatPair`) live in the self-contained 80-line file
  `SubNLogN/Challenge.lean` (`SHA-256: 7aa50930921c494e50803b037c4cc6ed9be880c3f795e4b171e16ab59cf61fb5`).
- Additional exported corollaries (`intMul_TM2_sub_nlogn_46`, `intMul_TM2_sub_nlogn_47`, `intMul_TM2_sub_nlogn_56`, and
  `intMul_TM2_littleO_nlogn`, where `_47` and `_56` follow from `_46` by exponent monotonicity `intMulSubNLogN_mono` while
  `SubNLogN/S5/Schedule.lean` checks the corresponding parameter-row slacks) and pure-`ℕ`/`ℤ` component checks (`S1`–`S5`,
  accompanying the full proofs in `SubNLogN/{Math,Machine,Assembly}` indexed in Table 7 of Section 8) are stated in
  `SubNLogN/Spec.lean` and assembled in `SubNLogN/Headline.lean`.
- `SPEC_LOCK.sha256` records **both** the full-file SHA-256 (`sha256sum -c SPEC_LOCK.sha256`) and the comment-stripped
  semantic SHA-256 (re-verified against `SPEC_LOCK.sha256` in standalone mode by
  `python3 -B tools/check_semantic_freeze.py`) of `SubNLogN/Spec.lean` and `SubNLogN/Challenge.lean`.

## Independent `O(n log n)` inner-multiplier formalization and numbering guide

- **Independent `[MS]` multiplier formalization**: The libraries `IntMul`, `IntMulTM`, `WP`, `Contracts`, and
  `LevelSync` (together with `IntMul.lean` and `AxiomCheck.lean`; `949` files, `184,759` lines; headline
  `IntMulTM.intMul_TM2_nlogn`) form an independent Lean 4 formalization of the two-dimensional multiplier of `[MS]`
  (*Integer multiplication in O(n log n) time on a single two-dimensional grid, with a formally verified proof*, 2026),
  developed for this paper and kernel-checked as part of it; `[MS]` distributes its own, separate Lean development
  (headline `IntMul.tmIntMul_evalsToInTime_n_log_n`).
- **Numbering guide**: Docstrings cite the numbering of the current versions of both papers, while Lean identifiers and
  file names keep historical names. For example, in `SubNLogN`, `prop71_final` proves Proposition A.11,
  `remark74_noncommutativity_and_unshuffle` witnesses Remark 6.4, `theorem9_5_machine_of_stage_prog` refers to an unused
  per-stage sufficient condition named after an earlier numbering of Theorem 1, and `SubNLogN/Machine/AppC` formalizes
  Appendix A; in `IntMul`, `Theorem1TwistedDuality` (`theorem1_*`) proves `[MS]` Proposition 4.1,
  `Theorem2PoissonIdentity` (`theorem2_*`) proves `[MS]` Theorem 4.2, `Theorem3BidiagonalAndSchedule` (`theorem3_*`,
  `lemma2_*`) proves `[MS]` Theorem 5.1, Lemma 5.2, Lemma 6.1, and Lemma 6.5, `Theorem4KroneckerSpread` (`theorem4_*`)
  proves `[MS]` Lemma 6.2 and Theorem 6.3, and `Theorem5ComplexityAndCorrectness` (`theorem5_*`) proves `[MS]` Theorem 1.
  Where modules (`IntMul/Theorem6And7Barriers.lean`, `WP/W15/*`, or executable-pipeline modules) discuss material from an
  earlier `[MS]` draft that is omitted in the current `[MS]`, docstrings describe the mathematical content directly
  without assigning an `[MS]` number.

## Trust base

Accepting the formal proof of `SubNLogN.Assembly.intMul_challenge` requires trusting only:

1. the Lean 4 kernel (`leanprover/lean4:v4.33.1`, pinned in `lean-toolchain`);
2. the Mathlib definitions referenced in `SubNLogN/Challenge.lean` at Mathlib commit `0df444a3`
   (`Turing.FinTM2`, `Turing.TM2ComputableInTime`, `Computability.encodeNat`, `Computability.decodeNat`,
   `encodingNatBool`, `Encoding`, and `Finite`, pinned in `lakefile.toml` and `lake-manifest.json`), together with
   `Nat.log2` in Lean core;
3. the 80-line statement file `SubNLogN/Challenge.lean` (importing only
   `Mathlib.Computability.TuringMachine.Computable` and `Mathlib.Computability.Encoding`); and
4. Lean's three standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.

Unlike the written proofs in Sections 4–7 of the paper (which take Facts 3.3–3.4 from `[OAI26]` as black boxes), the
Lean development assumes no result of `[OAI26]`, `[MS]`, or any other paper as an axiom or hypothesis: both $h = 100$
triple networks and their rank/deficit certificates, all multi-stack Turing machine procedures, the parameter-exposed
reductions of Appendix A, and the $O(N \log N)$ inner multiplier (`IntMulTM.intMul_TM2_nlogn`) are defined and proved in
Lean.

## Build

- Toolchain: `leanprover/lean4:v4.33.1` (`lean-toolchain`).
- Mathlib: commit `0df444a360eaa60ab8c11dca51a86af692955474` (`lakefile.toml`, `lake-manifest.json`).

```bash
lake exe cache get                      # prebuilt Mathlib oleans
lake build                              # default targets: AxiomCheck, Contracts, IntMul, IntMulTM, LevelSync, WP, SubNLogN
lake env lean SubNLogN/GateCheck.lean   # SubNLogN gate & #print axioms on intMul_challenge and all SubNLogN headlines
lake env lean IntMulTM/Headline.lean    # #assert_std_axioms & #print axioms on IntMulTM.intMul_TM2_nlogn
lake env lean AxiomCheck.lean           # #axiom_union IntMul & #print axioms on IntMul headline
```

*(On high-core-count Linux hosts where 64+ concurrent `lean` workers exceed the system-wide `fs.file-max` open-file
limit via `mmap`ed `.olean` files, cap worker fan-out with `LEAN_NUM_THREADS=16 LEAN_IMPORT_WORKERS=4 lake build`.)*

## Verification & Manifests

- `SubNLogN/GateCheck.lean`, `IntMulTM/Headline.lean`, and `AxiomCheck.lean` verify respectively that:
  - `SubNLogN.Assembly.intMul_challenge` and all `SubNLogN` exported headlines (`SubNLogN/GateCheck.lean`, with zero
    errors or warnings across `SubNLogN`),
  - `IntMulTM.intMul_TM2_nlogn` (`IntMulTM/Headline.lean`), and
  - `IntMul.computablePaperMultiplyOfBitLength_correct_and_isBigO` together with all `5,116` constants under `IntMul`
    (`AxiomCheck.lean`)
  depend only on `[propext, Classical.choice, Quot.sound]`.
- `VERIFICATION_escape_scan.md` (regenerated by `tools/escape_scan.py`) scans all `2,011` library `.lean` files with
  comments and string literals stripped (excluding standalone replay wrappers and negative-control `.lean` files in
  `replay/`, which are not part of the `lake build` targets), confirming:
  - `0` `sorry`;
  - `0` `admit`;
  - `0` `axiom` declarations;
  - `0` `native_decide`;
  - `decide +kernel`: `41` occurrences in `5` files under `SubNLogN/Math/Networks` (kernel reduction; not `native_decide`; adds no axiom).
- `tools/check_semantic_freeze.py`: in standalone mode (`python3 -B tools/check_semantic_freeze.py`), re-verifies all
  `2,011` library `.lean` files (`replay/` excluded as non-library) against `MANIFEST_stripped.sha256`, balanced comment
  delimiters, `SPEC_LOCK.sha256`, and the exact SHA-256 of `SubNLogN/Challenge.lean`.
- `MANIFEST.sha256` (`sha256sum -c MANIFEST.sha256`) records the SHA-256 of every `.lean` source file, build
  configuration file, `LICENSE`, `SPEC_LOCK.sha256`, `VERIFICATION_escape_scan.md`, `tools/*` script, and `replay/*`
  file (`2,076` entries total); its own SHA-256 begins with `b706618497aa`.
- External kernel-replay checks (`leanchecker` on all modules and on the full import closures of both headline modules; `comparator` with `nanoda`, including seven negative controls) were executed on this snapshot; commands, tool versions and logs are in `replay/`.

## Not included

- Build artifacts (`.lake/`).
