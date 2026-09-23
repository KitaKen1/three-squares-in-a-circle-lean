# Verification record

`result.json` records the successful isolated-copy build and audit completed on
2026-09-23. The copy used the pinned dependency checkout and its existing
`.olean` artifacts; it rebuilt the project and then checked 441 declarations,
FC-definition provenance, and the final `IsLeast` theorem. It is not a
zero-cache rebuild of Mathlib and Formal Conjectures.

After that run, two module documentation comments were updated in the shipped
source (`ThreeSquares.lean` and `ThreeSquares/Target.lean`), and `verify.py` was
strengthened to hash the root module, audit scripts, and its own source. The
proof-bearing declarations did not change. The recorded source hashes therefore
refer to the pre-documentation-sync copy; regenerate the record from this
folder with `LEAN_NUM_THREADS=1 python3 verify.py` to bind a new result to the
current exact files. That exact-hash follow-up was not completed because Lake
started rebuilding the long representative-tree modules after the doc-only
change.

The Lean4Web browser run is tracked separately; see `../lean4web/README.md`.
