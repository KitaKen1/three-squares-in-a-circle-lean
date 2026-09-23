# Lean4Web edition

## Separate compressed candidate

`ThreeSquaresCompressed.lean` is the 443-leaf implementation, targeting
Lean v4.35.0-rc2. It replaces the recursive certificate-tree workload with
small algebraic and domain-cover proofs. The degree-four Bernstein identity
is proved once and reused at every triangle. The file imports only the needed Mathlib
modules and tactics. The 64 representative cases and the full FC target are
preserved. The original file below remains unchanged for comparison.

The new source is larger (about 1.69 MB versus 0.83 MB): it contains explicit
small lemmas instead of deeply nested data checked by one recursive evaluation.
A smaller source file is not the performance objective.

**The whole standalone source passed locally on Lean / Mathlib 4.33.1:**
586.752 seconds, peak RSS 4,694,867,968 bytes (4.37 GiB), at `-M5120` with one
worker. All 64 case reports and the two final theorem reports use only the
standard three axioms; the run has no errors or `sorryAx`.
The generator's local output is byte-identical to the tested source, with
SHA-256 `51cb97850e68b48983cdbf61e62bf6d0df54b212b8810414b377c391649e5522`.
The web output applies only the four documented Lean 4.35 alias replacements.
The separate Lake project also passed against the actual pinned FC definitions,
including the final exact-target and three-axiom audit; see
[`../lean/verification/compressed/result.json`](../lean/verification/compressed/result.json).
On 2026-09-24 the user reported that this compressed edition passed in
Lean4Web v4.35.0-rc2. Their final screenshot shows group 16/16 complete,
`#check` for the exact `IsLeast` theorem, and `#print axioms` for both final
theorems. Each displayed axiom list is exactly `propext`, `Classical.choice`,
and `Quot.sound`. See the saved images and checksums in
[`../lean/verification/compressed/browser-observation.json`](../lean/verification/compressed/browser-observation.json).
The visible source tail matches the generated file's final declarations. The
screenshots do not provide a browser-buffer hash, complete diagnostics export,
wall time, or memory measurement. Group progress alone would not establish the
final result; the screenshot includes both final axiom reports.

The generated certificate declarations use `fc_compact_decl`, a wrapper around
the ordinary Lean command elaborator that omits intermediate editor goal/hover
metadata. Kernel checking and error messages remain enabled. The two
unused/unreachable tactic linters, which depend on that metadata, are disabled.
For interactive inspection of a declaration, remove its `fc_compact_decl` prefix.
This trades detailed editor feedback for lower retained memory, without changing
the theorem or adding a proof axiom.

Regenerate this separate candidate from the repository root:

```sh
python3 lean4web/generate_compressed.py
```

`compressed-source-manifest.json` records the source hashes and generated-file
hash. The generation script can also write the unmodified 4.33 source for a
local test via `--local-output /path/to/file.lean`.

The user's 2026-09-24 00:25 screenshot shows that the preceding original edition,
including its split final check, also stopped with “Lean server has stopped.”
The displayed source location does not identify the command that failed, and
no final audit is shown for that run. The screenshot does not concern this new
compressed candidate.

## Original edition


`ThreeSquaresLean4Web.lean` is generated as a single source file from the 54
modules in the dependency closure of the upper bound, FC target bridge, and
representative-tree proof in `../lean/`. It starts with `import Mathlib`,
includes the full proof source, and ends by checking and printing the axioms of
the unconditional lower bound and FC `IsLeast` theorem.

The file embeds the four definitions (`Square`, `UnitSquare`, `Circle`, and
`Packing`) from Formal Conjectures' `Wikipedia/SquarePacking.lean` at the exact
commit pinned by the main project. The FC-compatible project in `../lean/`
imports that module directly and is the authoritative integration check.

## Toolchain

`lean-toolchain` pins local Lean/Elan use to `leanprover/lean4:v4.35.0-rc2`.
For the web editor, select the same Lean release and use its matching Mathlib
environment, then load `ThreeSquaresLean4Web.lean`. The final output should
include the theorem signatures and only `propext`, `Classical.choice`, and
`Quot.sound` in each axiom report.

Regenerate from the repository root with:

```sh
python3 lean4web/generate_source.py
```

The full FC-compatible build and 441-declaration audit are run in `../lean/`.
The Lean 4.35.0-rc2 toolchain selection and deterministic generation are
verified locally. Browser feedback caught two standalone-file issues: `import`
must be the first command, and the target's `ℝ²` notation is scoped by an FC
geometry utility that is not imported into a single-file editor. The generator
now puts `import Mathlib` on line 1 and embeds that notation with its original
meaning. It also gives formerly private declarations ordinary unique names to
avoid Lean4Web style warnings.

User-provided screenshots dated 2026-09-23 22:03 JST show both final theorem
signatures and their axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound` in Lean4Web v4.35.0-rc2. Those outputs establish that the shown
theorems were accepted in the environment that produced them. The screenshots
also show `Processing stopped`; they do not establish its cause or certify a
stable, error-free editor session. The browser source hash and complete
diagnostics were not independently exported.

The displayed `if_pos`, `if_neg`, `if_true`, and `if_false` messages are
deprecation warnings. The generator now emits their Lean 4.35 replacements
`ite_eq_left`, `ite_eq_right`, `ite_true`, and `ite_false`. This is a name-only
compatibility change, not a speedup. The successful screenshot outputs concern
the preceding version; they do not certify subsequent generated files. The
pinned FC project's sources are unaffected.

## Server crash and bounded verification

The later user screenshots (2026-09-23 23:07–23:10 JST) show only the lower-bound
signature followed by an explicit Lean server crash. They do **not** show the
final axiom reports for that run. The server's generic "stack overflow or a
bug" message does not identify the cause.

A local Lean 4.33.1 test isolated the code **after** `tree363`. With one worker
and `-M6144`, the original tail aborted with a memory exception during
`word_reaches_rep`, the 512-branch correspondence check. The same check failed
under that limit even without importing the 64 certificate trees. This is a
local memory-limit reproduction, not proof of the remote server's cause or
memory limit.

The generator now replaces that one large computation with 16 kernel-checked
blocks of 32 cases. A quotient/remainder proof covers every code below 512 and
proves the **original** `word_reaches_rep` statement. The correspondence table,
lookup, 64 certificate trees, FC definitions, and final theorem statements are
unchanged. All checks still use `decide +kernel`; the final two `#print axioms`
commands remain. The browser edition also sets `Elab.async false` and prints
progress at the 16 certificate groups and four final assembly stages.

The modified final module passed locally in 21.44 seconds. The final module
extracted from the actual generated artifact was also checked, using already
checked certificate-tree imports: 50.30 seconds, peak RSS about 5.86 GiB, under
the same 6 GiB setting. Both final theorems reported only `propext`, `Classical.choice`,
and `Quot.sound`. These numbers cover **the final module**, including imports,
not the full proof. The approximately hour-long certificate work has not been
eliminated. The generic 16-by-32 coverage argument was also checked with the
actual Lean v4.35.0-rc2 toolchain.

A separate attempt to recheck the first four certificate trees still failed
with a memory exception at the `-M6144` setting (peak RSS about 7.36 GiB before
termination). Lean's setting is not a strict operating-system memory cap.
The tail improvement does not establish that the entire proof fits in 6 GiB.

The revised original single file has not completed a Lean4Web v4.35.0-rc2 run.
Do not infer whole-file completion from a theorem signature or a progress
message; inspect all diagnostics and both final axiom reports.
