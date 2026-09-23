# Certificate data and benchmarks

This directory holds the deterministic certificate-search inputs, generated
residual data, and hash/timing record used by `verify.py`. These bounded-search
experiments are auxiliary artifacts; the historical field
`global_lower_bound_proved: false` in `benchmark.json` describes that benchmark
generator's search cases, not the completed global theorem.

The unrestricted lower-bound proof is in `../ThreeSquares/RepTrees.lean` and
the 16 files under `../ThreeSquares/RepTrees/`. Those 64 representative trees
cover all 512 signed separation branches and are checked by the Lean kernel.
The theorem `ThreeSquares.least_three_square_packing_in_circle` assembles them
with the matching upper bound.

Regenerate the auxiliary benchmark from this directory's parent with:

```sh
python3 benchmark_certificates.py
python3 verify.py
```
