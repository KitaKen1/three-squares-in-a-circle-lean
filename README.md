# Three unit squares in a circle: an exact Lean proof

This repository proves that the least radius of a circle containing three
non-overlapping unit squares, with arbitrary rotations and reflections, is

$$
R_{\min}=\frac{5\sqrt{17}}{16}.
$$

The `lean/` project proves the statement against the definitions in the pinned
[Formal Conjectures square-packing module](https://github.com/google-deepmind/formal-conjectures/blob/8927a585c5d522fc132d7ea6488fcd9e30ccd80e/FormalConjectures/Wikipedia/SquarePacking.lean).
The proof covers every placement, including asymmetric ones. Its compressed
version checks 64 representative cases and proves that they cover all 512
separation branches.

**Try it in Lean4Web:** [open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fthree-squares-in-a-circle-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FThreeSquaresCompressed.lean)
and select Lean/mathlib `v4.35.0-rc2`. This single-file edition includes the
final theorem and `#print axioms` checks. The successful browser run is recorded
in [the final screenshots and their hashes](lean/verification/compressed/browser-observation.json),
which show the 16/16 checkpoint and both axiom reports.

## Formal Conjectures target

The compressed project's final theorem is
[`ThreeSquares.CenterElimination.Compressed.least_three_square_packing_in_circle`](lean/ThreeSquares/Compressed/Main.lean):

```lean
theorem least_three_square_packing_in_circle :
    IsLeast {r : ℝ≥0 | Nonempty (Packing 3 UnitSquare (Circle r))}
      ((5 * NNReal.sqrt 17) / 16)
```

Here `Packing`, `UnitSquare`, and `Circle` are imported from
`FormalConjectures.Wikipedia.SquarePacking`. The [integration audit](lean/CompressedAudit.lean)
checks the origin of all four FC definitions, including `Square`, and confirms
that the feasible-radius set is definitionally the one in the pinned FC target.
The two upstream conjecture declarations still contain `sorryAx`; the proof
establishes a separate theorem and never uses those declarations as premises.

The original, larger implementation also proves
[`ThreeSquares.least_three_square_packing_in_circle`](lean/ThreeSquares/RepTrees.lean).
Both proofs have the same exact-radius conclusion. The compressed implementation
is the recommended one for the single-file browser edition.

## Mathematical explanation (AI generated)

An explicit placement gives the upper bound $R_{\min}\le5\sqrt{17}/16$.
For the lower bound, assume that some packing fits in a smaller circle. The
packing is normalized, and non-overlap gives one of 512 separation branches.
Proved symmetries reduce these to 64 representatives.

A weighted average of the squared vertex distances removes the unknown circle
center. Its value would be strictly below $425/256=(5\sqrt{17}/16)^2$ in a
smaller circle. After choosing signs for the relevant separating directions,
the same lower expression uses only seven coefficients and the two remaining
square angles. Rational rotation parameters $s,t$ clear the trigonometric
functions, leaving a polynomial

$$
N(s,t)=(1+s^2)(1+t^2)\bigl(L_\sigma(s,t)-425/256\bigr).
$$

Both factors outside the parentheses are positive. Thus $N\ge0$ rules out
the proposed smaller packing. Lean proves this on a finite cover: 443 domain
exclusions, using 636 nondegenerate triangles and 20 point domains. A shared
degree-four Bernstein identity turns each triangle check into 15 exact rational
coefficient-sign checks. The domain-cover and symmetry proofs then assemble the
global lower bound and the matching upper bound into `IsLeast`.

Python generated the candidate certificates and source files. Their validity
is checked by Lean with ordinary proofs and `decide +kernel`; the Python search
is not a proof assumption. The final theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Files

| Path | Purpose |
| --- | --- |
| [`lean/`](lean/) | Lean 4.33.1 project importing the pinned FC definitions. |
| [`lean/ThreeSquares/Compressed/`](lean/ThreeSquares/Compressed/) | Compressed lower bound, shared polynomial identity, 16 groups of cases, and final theorem. |
| [`lean4web/ThreeSquaresCompressed.lean`](lean4web/ThreeSquaresCompressed.lean) | Generated single-file edition for Lean4Web v4.35.0-rc2. |
| [`lean/verification/compressed/`](lean/verification/compressed/) | Source hashes, module logs, FC audit, standalone measurement, and browser screenshots. |
| [`lean4web/ThreeSquaresLean4Web.lean`](lean4web/ThreeSquaresLean4Web.lean) | Preserved original 3,928-leaf edition. |

The browser file embeds the four FC definitions needed in a single source file.
The `lean/` project is the check against the actual imported FC module. See the
[`lean/` README](lean/README.md) and [`lean4web/` README](lean4web/README.md)
for module-level and browser-specific details.

## Verification

From this repository's root, build the compressed FC proof and run its audit:

```sh
cd lean
lake update
lake exe cache get
python3 scripts/build_compressed_sequential.py
```

The script builds the target's dependency closure one module at a time with one
Lean worker, then checks definition provenance, the exact FC feasible set, and
the final transitive axiom dependencies. It does not require running the
certificate generator. `--plan` lists the modules before building.

The recorded local checks used Lean/mathlib `v4.33.1` and Formal Conjectures
commit `8927a585c5d522fc132d7ea6488fcd9e30ccd80e`:

| Check | Recorded result |
| --- | --- |
| Full standalone source | Passed in 586.752 seconds; peak RSS 4.37 GiB; all 64 cases and both final theorems checked. |
| FC project | All 21 new modules passed against pinned FC dependencies; the integration audit confirmed the exact target and standard-three-only final axioms. Existing dependency caches were used. |
| Lean4Web v4.35.0-rc2 | User-reported completion; final screenshots show group 16/16, the `IsLeast` type, and both standard-three axiom reports. |

The [result record](lean/verification/compressed/result.json) and
[verification notes](lean/verification/compressed/README.md) identify the tested
sources and logs. The browser screenshots do not include a hash of the editor
buffer, a complete diagnostic export, elapsed time, or peak memory.
The earlier implementation has its own [441-declaration audit](lean/verification/result.json);
that record refers to its separate proof source.

## Status boundary

**Solved in this repository:** the exact three-square minimum for the pinned FC
definitions, including arbitrary rotations and reflections. The pinned FC
source itself is not edited here. The proof does not assert uniqueness of all
optimal configurations or solve the problem for other numbers of squares.

**Outside this result:** the uniqueness of optimal configurations, other
numbers of squares, and any change to the official FC category or its pinned
`answer(sorry)` declarations. This repository proves a separately named
theorem over the actual FC definitions.

## Sources and provenance

- [Formal Conjectures `Wikipedia/SquarePacking.lean`, pinned commit
  `8927a585c5d522fc132d7ea6488fcd9e30ccd80e`](https://github.com/google-deepmind/formal-conjectures/blob/8927a585c5d522fc132d7ea6488fcd9e30ccd80e/FormalConjectures/Wikipedia/SquarePacking.lean)
  supplies `Square`, `UnitSquare`, `Circle`, `Packing`, and the target
  conjectures. [`CompressedAudit.lean`](lean/CompressedAudit.lean) checks their
  origin, the feasible-radius set, and the final axioms. The imported FC
  definitions retain their upstream [Apache-2.0 license](lean/LICENSE-FC).
- [`lean-toolchain`](lean/lean-toolchain) and
  [`lakefile.toml`](lean/lakefile.toml) pin Lean 4.33.1 and the dependencies
  used for the FC project. The separate
  [`lean4web/lean-toolchain`](lean4web/lean-toolchain) selects 4.35.0-rc2.
- [Erich Friedman's *Squares in Circles*](https://erich-friedman.github.io/packing/squincir/)
  records the radius $5\sqrt{17}/16$ for a three-square packing and attributes
  the arrangement to 1997. Its construction supplies the known upper-bound
  target; the upper bound is checked again in
  [`UpperBound.lean`](lean/ThreeSquares/UpperBound.lean).
- [Montanher, Neumaier, Markót, Domes, and Schichl,
  *Rigorous packing of unit squares into a circle*, Theorem 2 and Table 6](https://link.springer.com/article/10.1007/s10898-018-0711-5)
  prove a rigorous interval for the optimum and enclose every optimal
  arrangement in four boxes. Their interval calculation and boxes are
  background results; they are not imported as axioms, Lean declarations, or
  certificate inputs in this proof.
- The exact lower-bound argument and finite certificates are in
  [`Bridge.lean`](lean/ThreeSquares/Compressed/Bridge.lean),
  [`Bernstein.lean`](lean/ThreeSquares/Compressed/Bernstein.lean),
  [`Domains.lean`](lean/ThreeSquares/Compressed/Domains.lean), and the
  [`Part00`–`Part15` modules](lean/ThreeSquares/Compressed/).
  [`input-manifest.json`](lean/verification/compressed/input-manifest.json)
  records the pinned source hashes;
  [`result.json`](lean/verification/compressed/result.json) and
  [`browser-observation.json`](lean/verification/compressed/browser-observation.json)
  record the local checks and the user-provided Lean4Web evidence.

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra.

## Appendix: difference from earlier results (AI generated)

The candidate radius was known exactly before this formalization. Friedman
exhibited a packing with radius $5\sqrt{17}/16$ in 1997.
Montanher, Neumaier, Markót, Domes, and Schichl later gave a rigorous
computer-assisted treatment of three squares. Their Theorem 2 proves

$$
1.28847050800547\le r_3\le1.28847050800553
$$

and encloses every optimal arrangement in four small parameter boxes. The
interval has width $6\times10^{-14}$ and contains
$5\sqrt{17}/16\approx1.2884705080055189$. The paper describes the
three-square case as solved. These are substantial prior results.

| Earlier result | What this repository adds |
| --- | --- |
| Friedman's exact candidate packing | A Lean proof that its radius is minimal among **all** freely placed three-square packings. |
| Montanher et al.'s rigorous interval and four boxes | An exact equality $r_3=5\sqrt{17}/16$ in Lean. The global lower-bound proof uses its own center-elimination and rational certificates; it does not import the paper's interval boxes or computation as axioms. |
| The pinned FC `IsLeast` conjecture | A separately named proof using the actual FC definitions, with the feasible set and final axiom dependencies audited. |

The published interval leaves a strictly positive gap between its lower
endpoint and the exact candidate. This repository closes that gap for the
stated FC minimum.
