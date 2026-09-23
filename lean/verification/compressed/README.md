# Compressed proof verification

`standalone-result.json` and `standalone433.log` record the successful complete
single-file check on Lean / Mathlib 4.33.1. It took 586.752 seconds and peaked at
4,694,867,968 bytes RSS, with one worker and `-M5120`. The full project proof
source is included; project proof modules are not imported in this test.
Four FC definitions are embedded for this standalone edition.

To regenerate and check the exact tested source:

```sh
python3 ../lean4web/generate_compressed.py --local-output /tmp/ThreeSquares433.lean
LEAN_NUM_THREADS=1 lake env lean -M5120 /tmp/ThreeSquares433.lean
```

Run these commands from the repository's `lean` directory.
The source SHA-256 should be
`51cb97850e68b48983cdbf61e62bf6d0df54b212b8810414b377c391649e5522`.

The actual-FC project audit also passed. `fc-result.json` records 21 new
modules checked sequentially against the pinned, previously built dependency
artifacts: total module wall time 768.509 seconds, peak RSS 6,457,016,320 bytes
(6.01 GiB). This includes repeated imports and is not a clean dependency build.
The separate integration audit took 12.721 seconds; `CompressedIntegration.log`
confirms all four FC definition origins, the actual feasible-radius set, the
exact answer, and standard-three-only transitive axioms for both final theorems.
Its two `sorryAx` lines are intentional negative controls for the upstream
unproved conjectures, which are not dependencies of our final proof.

`result.json` summarizes both checks; `input-manifest.json` and the module
records identify the exact sources. `modules/` contains the 21 module logs.
Rebuild using `python3 scripts/build_compressed_sequential.py` from `lean/`.
The original 441-declaration record in the parent folder concerns the original
proof. On 2026-09-24 the user reported that the compressed single-file source
passed in Lean4Web v4.35.0-rc2. The final screenshots show the 16/16 checkpoint,
the exact `IsLeast` type, and both final `#print axioms` reports containing only
`propext`, `Classical.choice`, and `Quot.sound`. The four screenshots and their
hashes are saved in `browser-evidence/` and `browser-observation.json`.
The screenshots do not export the complete browser diagnostics or a hash of the
editor buffer; browser elapsed time and peak memory were not measured.
