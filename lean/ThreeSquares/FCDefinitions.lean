import FormalConjectures.Wikipedia.SquarePacking

/-! # The upstream Formal Conjectures packing definitions

This module imports the actual FC module pinned in `lakefile.toml` at commit
`8927a585c5d522fc132d7ea6488fcd9e30ccd80e`. No definitions are duplicated here.

The imported FC module also contains unproved conjectures. Our proofs must not
use those conjectures: `Audit.lean` checks the transitive axiom dependencies.
-/
