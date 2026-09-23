# Three unit squares in a circle (Formal Conjectures target)

This Lean project proves the exact minimum radius for packing three freely
rotated unit squares into a circle. It imports the definitions from the pinned
Formal Conjectures module `FormalConjectures.Wikipedia.SquarePacking` and does
not replace the target by a locally redefined conjecture.

## Result

The unconditional theorem is

```lean
ThreeSquares.least_three_square_packing_in_circle
```

It proves that the least feasible radius is `5 * sqrt 17 / 16`. In particular,
the result allows arbitrary rotations and reflections of all three squares.
The matching upper bound is constructed explicitly. For the lower bound, every
possible separation branch is reduced by proved symmetries to one of 64
representative certificate trees; the trees have 3,928 leaves in total and are
checked by Lean. The final theorem is assembled against the actual FC `Packing`,
`UnitSquare`, and `Circle` definitions.

## Compressed target

The alternative target is `ThreeSquares.Compressed.Main`, with final theorem
`ThreeSquares.CenterElimination.Compressed.least_three_square_packing_in_circle`.
It checks 443 domain exclusions instead of the original 3,928 leaves.
All 21 new modules passed against the pinned FC dependency artifacts on Lean
4.33.1. `CompressedAudit.lean` confirmed the actual FC definitions, feasible
set, exact radius, and only `propext`, `Classical.choice`, and `Quot.sound` for
both final theorems. Separately, the complete standalone source passed in
586.752 seconds with peak RSS 4.37 GiB. See `verification/compressed/result.json`
in the distribution. The existing 441-declaration record belongs to the
original proof. The user subsequently completed the compressed browser edition
on Lean4Web v4.35.0-rc2; final theorem and axiom outputs are recorded in
`verification/compressed/browser-observation.json`.

Run `python3 scripts/build_compressed_sequential.py` after dependency setup.
It builds the required modules sequentially and runs `CompressedAudit.lean`.
Use `--plan` to list the dependency closure without running Lean. The original
root target `ThreeSquares` still builds the original proof.

## Reproduce

The FC-compatible project is pinned to Lean 4.33.1, mathlib 4.33.1, and FC
commit `8927a585c5d522fc132d7ea6488fcd9e30ccd80e`.

```sh
lake update
lake exe cache get
LEAN_NUM_THREADS=1 lake --wfail build ThreeSquares
LEAN_NUM_THREADS=1 python3 verify.py
```

`verify.py` checks the pinned FC checkout and certificate hashes, builds the
project, audits 441 declarations for transitive axiom dependencies, and checks
the connection to the upstream FC definitions. The audited project theorems
use only `propext`, `Classical.choice`, and `Quot.sound`; the audit found no
`sorryAx` dependency. The complete result is recorded in
`verification/result.json`. The current checked-in result was produced from the
main development checkout; a fresh, zero-cache rebuild of every dependency is
tracked separately and must not be inferred from that result.

## Layout

- `ThreeSquares/RepTrees.lean`: symmetry reduction, certificate-tree assembly,
  the unrestricted lower bound, and the final FC `IsLeast` theorem.
- `ThreeSquares/RepTrees/Part*.lean`: the 64 representative trees, split into
  16 modules to keep each kernel check bounded.
- `ThreeSquares/BranchSymmetry.lean`: finite encoding and the 512-to-64 branch
  reduction.
- `ThreeSquares/UpperBound.lean`: explicit matching packing.
- `Audit.lean`, `IntegrationAudit.lean`, and `verify.py`: reproducible proof and
  FC-integration checks.
- `certificates/`: exact certificate inputs, generator outputs, and benchmark
  hashes.

`lean4web/` at the repository root contains a generated single-file edition
targeting Lean 4.35.0-rc2. It embeds the four FC definitions needed to state the
same target and the full local proof source. The FC-compatible Lake project in
this directory remains the authoritative build and audit against the pinned FC
library.

## Reference

The submission layout follows the FC-target-plus-Lean4Web approach used by
[KitaKen1/erdos-361-asymptotic](https://github.com/KitaKen1/erdos-361-asymptotic).
The related Formal Conjectures submission is
[PR #4944](https://github.com/google-deepmind/formal-conjectures/pull/4944).
